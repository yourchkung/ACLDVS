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
#class CLSZH(BLSAggregation):
class CLSZH:
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
        global H
        H= lambda a: group.hash(str(a), ZR)
       
    @staticmethod
    def dump(obj):
        return objectToBytes(obj, group)
    
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
        g2 = group.random(G2)      # generator for group G of prime order p
        g1 = group.random(G1)   
        a = group.random(ZR)  #from Zp
        W2    = g2 ** a      # G1 
        W1  = g1 ** a      # G1
        P= (pair(g1,g2)) ** a
        pk = {'g2':g2,'W2':W2, 'g1':g1,'W1':W1, 'P':P }

        sk = {'a':a} #master secret
        if debug: 
            print(sk)
            print(pk)
        
        return (pk, sk)
        
  
    def extractPPK(self, pkk, skk, IDU):
        '''  extract the secretkey'''
        ru = group.random(ZR)
        a=skk['a']
        g2=pkk['g2']
        W2=pkk['W2']
        g1=pkk['g1']
        W1=pkk['W1']
        #Tu = pkk['g'] ** uu
        #ID=self.dump()
        m={'ID':IDU}
        MID=self.dump(m)
        hid=H(MID)
        R1=g1**ru
        R2=g2**ru
        #mm={'ID':IDU}
        #MM=self.dump(mm)
        #Q2=H3(MM)
        #D2=Q2**a
        Y1= g1**((a*hid)/(hid+ru+a))
        Y2= g2**((a*hid)/(hid+ru+a))
        
              
        if debug:
            print("sk    =>", R1)
            print("pk    =>",  Y1)
            #print ("ID-PKK---%s"%M)
        return {'pk1':Y1 , 'pk2':Y2,  'sk1':R1,  'sk2':R2 }
        
    def extractKey(self, kpk, ppk, IDU):
        #  user key generation
        #nu = group.random(ZR)
        x = group.random(ZR)
        #yu = group.random(ZR)
        z = group.random(ZR)
        Y1=ppk['pk1']
        Y2=ppk['pk2']
        R1=ppk['sk1']
        R2=ppk['sk2']
        #g2=kpk['g2']
        #W2=kpk['W2']
        #g1=kpk['g1']
       # W1=kpk['W1']
        P=kpk['P']
        # public key

        X1=Y1**(1/x)
        X2=Y2**(1/x)
        Z=P**z
                
        pk =  {'X1': X1 , 'X2': X2 , 'Z':Z}
        sk =  {'R1': R1 ,'R2': R2 ,  'x':x, 'z':z}
        if debug:
            print("pk    =>", pk)
            print("sk    =>", sk)
            
        return (pk, sk)  

    def sign(self, pk, spk, ssk, IDS, M): 
        g2=pk['g2']
        W2=pk['W2']
        #g1=pk['g1']
        #W1=pk['W1']
        P=pk['P']
        #R1=ssk['R1']
        R2=ssk['R2']
        x=ssk['x']
        z=ssk['z']
        t = group.random(ZR)
        m={'ID':IDS}
        MID=self.dump(m)
        hid=H(MID)
        mm={'M':M}
        MM=self.dump(mm)
        hm=H(MM)
        Q1= P**t
        Q2= ((g2**hid)*R2*W2)**(((z/hm)-t)*x)
 
        
        return (IDS, spk, Q1, Q2)

##    def aggregate_sigma(self, pubkey_signatures):
##        # This method of aggregation is resistant to rogue public key attack
##        #qs = []
##        #Rs = []
##        all_id_pubkeys = [ (i[0] , i[1], i[2] ) for i in pubkey_signatures]
##        if debug:
##            print (all_id_pubkeys)
##        #all_ID = [i[0] for i in pubkey_signatures]
##        qs = [(i[3]) for i in pubkey_signatures]
##        #for sig in all_signatures:
##             #qs.append(sig['q'])
##             #qs.append(sig)
##             #Rs.append(sig['R'])             
##        #Asigma={'AQ':self.product(qs), 'AR': Rs}
##        n=len(qs)
##        if debug:
##            print("len of qs:")
##            print(n)
##            print(qs)
##            for IDS, spk, Rs in all_id_pubkeys:
##                print ("IDS-sign--%s"%IDS)
##                print ("spk-sign--%s"%spk)
##                print("Q2-Rs    =>", Rs)
##        if (n>1):
##            Asigma=self.product(qs)
##        elif (n==1):
##            Asigma=qs[0]
##        if debug:    
##            print ("Asigma---%s"%Asigma)    
##        return (all_id_pubkeys, Asigma)
          

        
    def varidate_pks(self,pk, pubkey_signatures):
        return 0
#        #all_id_pubkeys=Asignature[0]
#        g2=pk['g2']
#        W2=pk['W2']
#        g1=pk['g1']
#        W1=pk['W1']
#        P=pk['P']
#        
#        k=[(i[0], i[1]) for i in pubkey_signatures] 
#        for ID, spk in k:
#            X1=spk['X1']
#            Y=spk['Y']
#            T1=pair(X1,W)
#            T2=pair(g1,Y)
#            if T1!=T2:
#               print ("Error check vpk not pass: "+ID)
    
    def varidate_ppks(self,pk, ppk, ID):
        #all_id_pubkeys=Asignature[0]
        g2=pk['g2']
        W2=pk['W2']
        g1=pk['g1']
        W1=pk['W1']
        #P=pk['P']
        
        Y1=ppk['pk1']
        #Y2=ppk['pk2']
        #R1=ppk['sk1']
        R2=ppk['sk2']
        m={'ID':ID}
        MID=self.dump(m)
        hid=H(MID)
        T1=(pair(g1,W2))**hid
        T2=pair(Y1,(((g2**hid)*R2)*W2))
        if T1!=T2:
            print ("Error check vpk not pass: "+ID)


    def verify(self, pk, pubkey_signatures, M):
         #g2=pk['g2']
         #W2=pk['W2']
         #g1=pk['g1']
         #W1=pk['W1']


            #------
         
         k=[(i[0], i[1], i[2], i[3]) for i in pubkey_signatures] 
         for ID, spk,Q1, Q2 in k:
            X1=spk['X1']
            #X2=spk['X2']
            Z=spk['Z']
            #mid={}            
            #------
            mid={'ID':ID }
            MID=self.dump(mid)
            hid=H(MID)
            mm={'M':M}
            MM=self.dump(mm)
            hm=H(MM)
            T1=(((Z**(1/hm))/Q1)**hid)
            T2=pair(X1, Q2)

            if (T1!=T2):
               #if T1!=T2:
               print ("Error verify not pass: "+ID)
               return False
               
         return True

def main():
    group = PairingGroup('MNT224')
    cldvs = CLSZH(group)
    (pk, sk) = cldvs.setup()
    #IDS = "bob@mail.com"
    #ID=CLDVS.dump(IDS)
    #group.hash(ID, ZR)    
    IDS = "bob@mail.com"
    #group.hash((IDS), ZR)
    sppk = cldvs.extractPPK(pk, sk, IDS)
    cldvs.varidate_ppks(pk, sppk, IDS)
    (spk, ssk)= cldvs.extractKey(pk, sppk, IDS)
    #IDV = "other@mail.com"
    #vppk = cldvs.extractPPK(pk, sk, IDV)
    #(vpk, vsk)= cldvs.extractKey(pk, vppk, IDV)
    M="I love PC"
    (IDI, spk, Q1, Q2)= cldvs.sign(pk, spk, ssk, IDS, M)
    Asig=[ (IDI, spk, Q1, Q2)]
    cldvs.varidate_ppks(pk, sppk, IDS)
    #(all_id_pubkeys, Asigma)=cldvs.aggregate_sigma( Asig)
    #Asignature= (all_id_pubkeys, Asigma)
    out=cldvs.verify(pk, Asig, M)
    print (out)
    assert out== True, "invalid signature"
    if debug: print("Successful Decryption!")
    
def maintest(num, gup):
    number=num
    data=[] 
    counter=1   
    group = PairingGroup(gup)
    cldvs = CLSZH(group)    
    (pk, sk) = cldvs.setup()
    #start with one random IDV 
    #IDV=randomStringGen(8)+"@mail.com"  
    #IDV = "other@mail.com"
    #vppk = cldvs.extractPPK(pk, sk, IDV)
    #(vpk, vsk)= cldvs.extractKey(pk, vppk, IDV)
    for i in range(1, number+1):
        Asig=[]
        keyextract=0
        sign=0
        validate=0
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
            (IDS, sspk, Q1, Q2)= cldvs.sign(pk, spk, ssk, IDI, Message)
            end=time.clock() 
            sign+=((end-start)*1000)
            Asig.append ((IDS, sspk, Q1, Q2))
            #--------------validate
            start=time.clock()        
            cldvs.varidate_ppks(pk, sppk,IDS)
            end=time.clock()         
            validate+=((end-start)*1000)    
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
        #start record varidate pk     
        start=time.clock()       
        #(all_id_pubkeys, Asigma)=cldvs.aggregate_sigma( Asig)  
        end=time.clock()         
        aggregate=((end-start)*1000)   
        #start record varidate pk     
        start=time.clock()                 
        out=cldvs.verify(pk, Asig, Message)
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

    fileout="CLSZH_data_"+gup+"_"+randomStringGen(2)+".csv"
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
