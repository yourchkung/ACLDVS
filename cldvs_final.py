'''
 
| From: "CLDVS"
| Available from: 

* type:			Designated verifier signature (identity-based)
* setting:		bilinear groups (asymmetric)

:Authors:	Pairat Thorncharoensri
:Date:			12/2019

''' 
from __future__ import print_function
from charm.toolbox.pairinggroup import PairingGroup,ZR,G1,G2,GT,pair
#from charm.toolbox.IBEnc import IBEnc
#from charm.toolbox.hash_module import Waters
from charm.schemes.aggrsign_bls import BLSAggregation
import math, string, random
from functools import reduce
from charm.core.engine.util import objectToBytes
import time 

def randomStringGen(size=30, chars=string.ascii_uppercase + string.digits):
    return ''.join(random.choice(chars) for x in range(size))

debug = False
#class CLDVS(BLSAggregation):
class CLDVS:
    """
    >>> from charm.toolbox.pairinggroup import PairingGroup,GT
    >>> from charm.toolbox.hash_module import Waters
    >>> group = PairingGroup('SS512')
    >>> waters_hash = Waters(group)
    >>> ibe = IBE_N04_z(group)
    >>> (master_public_key, master_key) = ibe.setup()
    >>> ID = "bob@mail.com"
    >>> kID = waters_hash.hash(ID)
    >>> secret_key = ibe.extract(master_key, ID)
    >>> msg = group.random(GT)
    >>> cipher_text = ibe.encrypt(master_public_key, ID, msg)
    >>> decrypted_msg = ibe.decrypt(master_public_key, secret_key, cipher_text)
    >>> decrypted_msg == msg
    True
    """
    
    """Implementation of CLDVS"""
    def __init__(self, groupObj):
        #BLSAggregation .__init__(self)
        global group
        group = groupObj
    
    def product(self, seq):
        #return reduce(lambda x, y: x * y, seq)
        sq = [i for i in seq]
        for i in range(0, len(sq)):
            #ii = group.random(G1)
            ii = seq[i]
            if (i==0):
                qs=ii
            else:    
                qs= qs * ii
        return qs
    
    def setup(self):
        """
        Generates public key and master secret key.
        """
        g = group.random(G1)      # generator for group G of prime order p
        a = group.random(ZR)  #from Zp
        W    = g ** a      # G1 
        pk = {'g':g,'W':W}

        sk = {'a':a} #master secret
        if debug: 
            print(sk)
            print(pk)
        
        return (pk, sk)
        
    @staticmethod     
    def dump(obj):
        return objectToBytes(obj, group)   
    def extractPPK(self, pkk, skk, IDU):
        '''  extract the secretkey'''
        uu = group.random(ZR)
        a=skk['a']
        Tu = pkk['g'] ** uu
        #ID=self.dump()
        m={'ID':IDU, 'T':Tu}
        M=self.dump(m)
        lu=group.hash(M, ZR)
        du=uu+lu*a
              
        if debug:
            print("Tu    =>", Tu)
            print("du    =>", du)
            print ("ID-PKK---%s"%M)
        return {'pk': Tu, 'sk':du}
        
    def extractKey(self, kpk, ppk, IDU):
        #  user key generation
        nu = group.random(ZR)
        xu = group.random(ZR)
        yu = group.random(ZR)
        zu = group.random(ZR)
        du=ppk['sk']
        g=kpk['g']
        # public key
        Xu=g**xu
        Yu=g**yu
        Zu=g**zu
        Tu = ppk['pk']
        Bu=g**nu
        
        #ID=self.dump()
        m={'ID':IDU, 'X': Xu, 'Y': Yu, 'Z': Zu, 'T': Tu,'B': Bu}
        M=self.dump(m)
        ru=group.hash(M, ZR)
        cu=(nu+(ru*du))
          
        pk = {'X': Xu, 'Y': Yu, 'Z': Zu, 'T': Tu,'B': Bu,'c': cu}
        sk =  {'x': xu, 'y': yu, 'z': zu, 'd': du}
        if debug:
            print("pk    =>", pk)
            print("sk    =>", sk)
            print ("M-key---%s"%M)
            mm={'ID':IDU, 'T':Tu}
            MID=self.dump(mm)
            
            lv=group.hash(MID, ZR)
            m2={'ID':IDU, 'X': Xu, 'Y': Yu, 'Z': Zu, 'T': Tu,'B': Bu}
            MG=self.dump(m2)
            gamma_v =group.hash(MG, ZR)
            temp1=g**cu
            temp2=Bu*((Tu * (kpk['W'] ** lv)) **gamma_v)
            print ("ID-key---%s"%MID)
            print ("MG-key---%s"%MG)
            if temp1!=temp2:
                print ("Error check extract not pass: "+IDU)
            else:
                print ("pass extract")
        return (pk, sk)  

    def sign(self, pk, spk, ssk, vpk, IDS, IDV, M): 

        g=pk['g']
        rs = group.random(ZR)
        m={'ID':IDV, 'T':vpk['T']}
        MIDV=self.dump(m)
        lv=group.hash(MIDV, ZR)
        m1={'ID':IDV, 'X': vpk['X'], 'Y': vpk['Y'], 'Z': vpk['Z'], 'T': vpk['T'],'B': vpk['B']}
        MG=self.dump(m1)
        gamma_v =group.hash(MG, ZR)
        temp1=g**vpk['c']
        temp2=vpk['B']*((vpk['T'] * (pk['W'] ** lv)) **gamma_v)
        if temp1!=temp2:
            print ("Error check vpk not pass in sign: "+IDV)
            
        Rs=g**rs
        m2={'M':M, 'R': Rs, 'YV_ZS': vpk['Y'] ** ssk['z'], 'pkv': vpk, 'pks': spk}
        MB=self.dump(m2)
        Beta=group.hash(MB, ZR)
        Rhat=((vpk['T']*(pk['W']**lv))**rs)*(vpk['Z']**(Beta*ssk['d']))
        m3={'M':M,'RH': Rhat,  'R': Rs, 'XV_YS': vpk['X'] ** ssk['y'], 'pkv': vpk, 'pks': spk}
        MA=self.dump(m3)
        alpha=group.hash(MA, ZR)  
        q=(vpk['Y'] ** rs)*Rhat*(vpk['X']**(alpha*(ssk['x']+ssk['z'])))
        # signature out
        #sigma={'q':q, 'R': Rs}
        if debug:
            print("signing")
            print("Q1-q    =>", q)

        #return (IDS, spk, sigma)
        if debug:
            print ("IDS-sign--%s"%IDS)
            print ("spk-sign--%s"%spk)
            print("Q2-Rs    =>", Rs)
            print ("MID-sign---%s"%MIDV)
            print ("m-sign---%s"%m)
            print ("MB-sign---%s"%MB)
            print ("MA-sign--%s"%MA)
        return (IDS, spk, Rs, q)

    def aggregate_sigma(self, pubkey_signatures):
        # This method of aggregation is resistant to rogue public key attack
        #qs = []
        #Rs = []
        all_id_pubkeys = [ (i[0] , i[1], i[2] ) for i in pubkey_signatures]
        if debug:
            print (all_id_pubkeys)
        #all_ID = [i[0] for i in pubkey_signatures]
        qs = [(i[3]) for i in pubkey_signatures]
        #for sig in all_signatures:
             #qs.append(sig['q'])
             #qs.append(sig)
             #Rs.append(sig['R'])             
        #Asigma={'AQ':self.product(qs), 'AR': Rs}
        n=len(qs)
        if debug:
            print("len of qs:")
            print(n)
            print(qs)
            for IDS, spk, Rs in all_id_pubkeys:
                print ("IDS-sign--%s"%IDS)
                print ("spk-sign--%s"%spk)
                print("Q2-Rs    =>", Rs)
        if (n>1):
            Asigma=self.product(qs)
        elif (n==1):
            Asigma=qs[0]
        if debug:    
            print ("Asigma---%s"%Asigma)    
        return (all_id_pubkeys, Asigma)
 

        
    def varidate_pks(self,pk, all_id_pubkeys):
        #all_id_pubkeys=Asignature[0]
        g=pk['g']
        if debug:
            print (all_id_pubkeys)
        k=[(i[0], i[1], i[2]) for i in all_id_pubkeys] 
        for ID, spk, R in k:
            m={'ID':ID, 'T':spk['T']}
            MID=self.dump(m)
            
            lv=group.hash(MID, ZR)
            m2={'ID':ID, 'X': spk['X'], 'Y': spk['Y'], 'Z': spk['Z'], 'T': spk['T'],'B': spk['B']}
            MG=self.dump(m2)
            gamma_v =group.hash(MG, ZR)
            temp1=g**spk['c']
            temp2=spk['B'] * ((spk['T'] * (pk['W'] ** lv)) **gamma_v)
            if temp1!=temp2:
                print ("Error check vpk not pass: "+ID)
            #else:
            #    print ("pass check vpk")
            if debug:
                print ("MID-ver---%s"%MID)
                print ("MG-ver---%s"%MG)

    def verify(self, pk, vsk, vpk,  IDV,all_id_pubkeys, Asigma, M):
         #g=pk['g']
         W=pk['W']
         #all_id_pubkeys=Asignature[0]
         #Asigma=Asignature[1]
         q1=Asigma
         #RS=Asigma['AR']
         RY_all=[]
         Rhat_all=[]
         XZ_all=[]
         k=[(i[0], i[1], i[2]) for i in all_id_pubkeys] 
         for ID, spk,Rs in k:
            m={}
            m={'ID':ID, 'T':spk['T']}
            MID=self.dump(m)
            lv=group.hash(MID, ZR)
            RY_all.append(Rs**vsk['y'])
            m1={'M':M, 'R': Rs, 'YV_ZS': spk['Z'] ** vsk['y'], 'pkv': vpk, 'pks': spk}
            MB=self.dump(m1)
            Beta=group.hash(MB, ZR)
            Rhat=(Rs**vsk['d'])*((spk['T']*(W**lv))**(Beta*vsk['z']))
            Rhat_all.append(Rhat)
            m2={'M':M,'RH': Rhat,  'R': Rs, 'XV_YS': spk['Y'] ** vsk['x'], 'pkv': vpk, 'pks': spk}
            MA=self.dump(m2)
            alpha=group.hash(MA, ZR)              
            XZ=((spk['X']*spk['Z'])**(alpha*(vsk['x'])))
            XZ_all.append(XZ)
            if debug:
                print ("ID-ver--%s"%ID)   
                print ("spk-ver--%s"%spk) 
                print ("RS-ver--%s"%Rs)
                print ("MID-ver--%s"%MID)  
                print ("m-ver--%s"%m) 
                print ("MA-ver--%s"%MA)                  
                print ("MB-ver---%s"%MB)
 
 
         n=len(RY_all)
         if debug:
            print("RY_all : {0}".format(n))
         if (n>1):
            qv=self.product(RY_all) * self.product(Rhat_all)*self.product(XZ_all)
         else:
            qv=RY_all[0]  * Rhat_all[0]* XZ_all[0]
         if debug:
            #print ("MB-ver---%s"%MB)
            #print ("MA-ver--%s"%MA)        
            print ("qv---%s"%qv)
            print ("q1---%s"%q1)
         return qv==q1

def main():
    group = PairingGroup('MNT224')
    cldvs = CLDVS(group)
    (pk, sk) = cldvs.setup()
    #IDS = "bob@mail.com"
    #ID=CLDVS.dump(IDS)
    #group.hash(ID, ZR)    
    IDS = "bob@mail.com"
    #group.hash((IDS), ZR)
    sppk = cldvs.extractPPK(pk, sk, IDS)
    (spk, ssk)= cldvs.extractKey(pk, sppk, IDS)
    IDV = "other@mail.com"
    vppk = cldvs.extractPPK(pk, sk, IDV)
    (vpk, vsk)= cldvs.extractKey(pk, vppk, IDV)
    M="I love PC"
    (IDI, spk, Rs, q)= cldvs.sign(pk, spk, ssk, vpk, IDS, IDV, M)
    Asig=[ (IDI, spk, Rs, q)]
    cldvs.varidate_pks(pk, Asig)
    (all_id_pubkeys, Asigma)=cldvs.aggregate_sigma( Asig)
    #Asignature= (all_id_pubkeys, Asigma)
    out=cldvs.verify(pk, vsk, vpk,  IDV,all_id_pubkeys, Asigma, M)
    print (out)
    assert out== True, "invalid signature"
    if debug: print("Successful Decryption!")
    
def maintest(num, gup):
    number=num
    data=[] 
    counter=1   
    group = PairingGroup(gup)
    cldvs = CLDVS(group)    
    (pk, sk) = cldvs.setup()
    #start with one random IDV 
    IDV=randomStringGen(8)+"@mail.com"  
    #IDV = "other@mail.com"
    vppk = cldvs.extractPPK(pk, sk, IDV)
    (vpk, vsk)= cldvs.extractKey(pk, vppk, IDV)
    for i in range(1, number+1):
        Asig=[]
        keyextract=0
        sign=0
        Message=randomStringGen()
        for j in range(0, i): 
            IDI=""
            IDI=randomStringGen(8)+"@mail.com" 
           #start record key gen 
            start=time.clock()   
            sppk = cldvs.extractPPK(pk, sk, IDI)
            (spk, ssk)= cldvs.extractKey(pk, sppk, IDI)
            end=time.clock() 
            keyextract+=((end-start)*1000)            
           #start record sign             
            start=time.clock()   
            (IDS, sspk, Rs, q)= cldvs.sign(pk, spk, ssk, vpk, IDI, IDV, Message)
            end=time.clock() 
            sign+=((end-start)*1000)
            Asig.append ((IDS, sspk, Rs, q))
            if debug:
                print("-------------------------------signatur number {0}:{1}------------------------------------".format(i, j))
                print ("IDI-sign--%s"%IDI)  
                print ("IDS-sign--%s"%IDS)   
                print ("spk-sign--%s"%spk)   
                print ("sspk-sign--%s"%sspk)   
                print("q--{0}: {0}".format(i, q))
                print("-------------------------------signatur number {0}:{1}------------------------------------".format(i, j))
        #start record varidate pk  
        #print(Asig) 
        #nn=len(Asig) 
        #print(nn) 
        start=time.clock()        
        cldvs.varidate_pks(pk, Asig)
        end=time.clock()         
        validate=((end-start)*1000)        
        #start record varidate pk     
        start=time.clock()       
        (all_id_pubkeys, Asigma)=cldvs.aggregate_sigma( Asig)  
        end=time.clock()         
        aggregate=((end-start)*1000)   
        #start record varidate pk     
        start=time.clock()                 
        out=cldvs.verify(pk, vsk, vpk,  IDV,all_id_pubkeys, Asigma, Message)
        end=time.clock()         
        verify=((end-start)*1000)   
        total=keyextract+sign+validate+aggregate+verify
        total_no_validate=keyextract+sign+aggregate+verify
        data.append( (counter, keyextract, sign, validate, aggregate, verify, total, total_no_validate) ) 
        counter+=1 
        if debug:
            print ("verify out for {:d} : {:}".format(counter-1,  out))      
        assert out== True, "invalid signature"
        if debug:
            #print("q--{0}: {0}".format(i, q))
            print("-------------------------------End verify signatur number {0}:{1}------------------------------------".format(i, j))
    fileout="ALCDVS_data_"+gup+"_"+randomStringGen(2)+".csv"
    f=open(fileout, "w+") 
    out="counter, keyextract, sign, validate, aggregate, verify, total, total_no_validate \n"
    f.write(out)
    for i in data:
        out="{:d},{:f},{:f},{:f},{:f},{:f},{:f},{:f} \n".format(i[0], i[1], i[2], i[3], i[4], i[5], i[6], i[7])
        f.write(out)

def mainindividual(num, gup):
    number=num
    data=[] 
    counter=1   
    group = PairingGroup(gup)
    cldvs = CLDVS(group)    
    (pk, sk) = cldvs.setup()
    #start with one random IDV 
    IDV=randomStringGen(8)+"@mail.com"  
    #IDV = "other@mail.com"
    vppk = cldvs.extractPPK(pk, sk, IDV)
    (vpk, vsk)= cldvs.extractKey(pk, vppk, IDV)
    for i in range(1, number+1):
        Asig=[]
        keyextract=0
        sign=0
        verify=0
        aggregate=0
        Message=randomStringGen()
        for j in range(0, i): 
            IDI=""
            IDI=randomStringGen(8)+"@mail.com" 
           #start record key gen 
            start=time.clock()   
            sppk = cldvs.extractPPK(pk, sk, IDI)
            (spk, ssk)= cldvs.extractKey(pk, sppk, IDI)
            end=time.clock() 
            keyextract+=((end-start)*1000)            
           #start record sign             
            start=time.clock()   
            (IDS, sspk, Rs, q)= cldvs.sign(pk, spk, ssk, vpk, IDI, IDV, Message)
            end=time.clock() 
            sign+=((end-start)*1000)
            Asig.append ((IDS, sspk, Rs, q))
            Asig2=[(IDS, sspk, Rs, q)]
            #start=time.clock()       
            (all_id_pubkeys2, Asigma2)=cldvs.aggregate_sigma( Asig2)  
            #end=time.clock()         
            #aggregate=((end-start)*1000)   
            #start record varidate pk     
            start=time.clock()                 
            out=cldvs.verify(pk, vsk, vpk,  IDV,all_id_pubkeys2, Asigma2, Message)
            end=time.clock()         
            verify+=((end-start)*1000)   
            if debug:
                print("-------------------------------signatur number {0}:{1}------------------------------------".format(i, j))
                print ("IDI-sign--%s"%IDI)  
                print ("IDS-sign--%s"%IDS)   
                print ("spk-sign--%s"%spk)   
                print ("sspk-sign--%s"%sspk)   
                print("q--{0}: {0}".format(i, q))
                print("-------------------------------signatur number {0}:{1}------------------------------------".format(i, j))
        #start record varidate pk  
        #print(Asig) 
        #nn=len(Asig) 
        #print(nn) 
        start=time.clock()        
        cldvs.varidate_pks(pk, Asig)
        end=time.clock()         
        validate=((end-start)*1000)        
        #start record varidate pk     
        start=time.clock()       
        (all_id_pubkeys, Asigma)=cldvs.aggregate_sigma( Asig)  
        end=time.clock()         
        aggregate=((end-start)*1000)   
#        #start record varidate pk     
#        start=time.clock()                 
#        out=cldvs.verify(pk, vsk, vpk,  IDV,all_id_pubkeys, Asigma, Message)
#        end=time.clock()         
#        verify=((end-start)*1000)   
        total=keyextract+sign+validate+aggregate+verify
        total_no_validate=keyextract+sign+aggregate+verify
        data.append( (counter, keyextract, sign, validate, aggregate, verify, total, total_no_validate) ) 
        counter+=1 
        if debug:
            print ("verify out for {:d} : {:}".format(counter-1,  out))      
        assert out== True, "invalid signature"
        if debug:
            #print("q--{0}: {0}".format(i, q))
            print("-------------------------------End verify signatur number {0}:{1}------------------------------------".format(i, j))
    fileout="CLDVS_data_inidividual_"+gup+"_"+randomStringGen(2)+".csv"
    f=open(fileout, "w+") 
    out="counter, keyextract, sign, validate, aggregate, verify, total, total_no_validate \n"
    f.write(out)
    for i in data:
        out="{:d},{:f},{:f},{:f},{:f},{:f},{:f},{:f} \n".format(i[0], i[1], i[2], i[3], i[4], i[5], i[6], i[7])
        f.write(out)



if __name__ == "__main__":
    debug = True
    main()
print("---------------------------------------------------------------------------")    
debug=False
#gup='MNT224'
gup='SS512'
maintest(500,gup)
#mainindividual(250, gup)
print("end")
