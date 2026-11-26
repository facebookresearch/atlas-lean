# Single-key weakly compact public-key functional encryption

A public-key functional encryption scheme for a circuit class $\{\mathcal{C}_{n,s}\}$ (inputs of length $n$, size $s$) has algorithms $\mathsf{Setup}(1^\lambda)\to(\mathsf{mpk},\mathsf{msk})$, $\mathsf{KeyGen}(\mathsf{msk},C)\to\mathsf{sk}_C$, $\mathsf{Enc}(\mathsf{mpk},x)\to\mathsf{ct}$ and $\mathsf{Dec}(\mathsf{sk}_C,\mathsf{ct})=C(x)$. It is *single-key selectively secure* if for every efficient adversary declaring $x_0,x_1$ and then one circuit $C$ with $C(x_0)=C(x_1)$, encryptions of $x_0$ and $x_1$ are indistinguishable given $\mathsf{mpk}$ and $\mathsf{sk}_C$. It is *weakly compact* (sublinear) if the encryption circuit has size $\mathrm{poly}(\lambda,n)\cdot s^{1-\epsilon}$ for a constant $\epsilon>0$, and *fully compact* if its size is $\mathrm{poly}(\lambda,n,\log s)$. Security with *sub-exponential* advantage means the advantage is at most $2^{-\lambda^{c}}$ for a constant $c>0$.

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../../../security-games/semantic-security-and-indistinguishability/ind-secure.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Prabhanjan Ananth, Abhishek Jain, "Indistinguishability Obfuscation from Compact Functional Encryption", CRYPTO (2015), IACR ePrint 2015/173.
- Nir Bitansky, Vinod Vaikuntanathan, "Indistinguishability Obfuscation from Functional Encryption", FOCS (2015), IACR ePrint 2015/163.
- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
