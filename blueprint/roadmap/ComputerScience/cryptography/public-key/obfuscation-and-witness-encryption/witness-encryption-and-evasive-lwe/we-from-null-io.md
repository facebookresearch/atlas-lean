# Witness encryption from null indistinguishability obfuscation

Let $\mathcal{O}$ be a null-iO obfuscator for polynomial-size circuits. For an NP relation $R$, define $\mathsf{Enc}(x,b)=\mathcal{O}(C_{x,b})$ for $b\in\{0,1\}$, where $C_{x,b}(w)=1$ iff $b=1$ and $R(x,w)=1$ (padded to equal size), and decrypt by evaluating on the witness. Then this is a witness encryption scheme for bits. In particular, indistinguishability obfuscation implies witness encryption for NP.

## Proof sketch

Correctness: on a witness, $C_{x,1}(w)=1$ and $C_{x,0}(w)=0$. Security: if $x\notin L$, both $C_{x,0}$ and $C_{x,1}$ output $0$ everywhere, so they are null circuits and null-iO makes their obfuscations indistinguishable. Multi-bit messages follow by encrypting bitwise.

## Depends on

- [Witness encryption for NP languages](witness-encryption.md)
- [Null indistinguishability obfuscation](null-io.md)

## Sources

- Sanjam Garg, Craig Gentry, Amit Sahai, Brent Waters, "Witness Encryption and its Applications", STOC (2013), IACR ePrint 2013/258.
- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022).
