# Public-key encryption from witness encryption and a PRG

Let $\mathrm{PRG}:\{0,1\}^{\lambda}\to\{0,1\}^{2\lambda}$ and let $\mathsf{WE}$ be witness encryption for the NP language $L=\{y:\exists s,\ \mathrm{PRG}(s)=y\}$. The scheme with secret key $s$, public key $y=\mathrm{PRG}(s)$, encryption $\mathsf{WE.Enc}(y,m)$ and decryption with witness $s$ is IND-CPA secure.

## Proof sketch

By PRG security, replace $y$ by a uniform $2\lambda$-bit string; with probability at least $1-2^{-\lambda}$ it lies outside the image of the PRG, i.e., $y\notin L$, and then witness-encryption security makes encryptions of any two messages indistinguishable.

## Depends on

- [Witness encryption for NP languages](witness-encryption.md)

## Proof depends on

- [Pseudorandom generators exist if and only if one-way functions exist](../../../symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Sanjam Garg, Craig Gentry, Amit Sahai, Brent Waters, "Witness Encryption and its Applications", STOC (2013), IACR ePrint 2013/258.
