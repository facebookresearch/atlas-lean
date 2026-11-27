# Witness encryption for NP languages

Let $L$ be an NP language with polynomial-time relation $R$. A *witness encryption* scheme for $L$ consists of $\mathsf{Enc}(1^\lambda,x,m)\to\mathsf{ct}$ and $\mathsf{Dec}(\mathsf{ct},w)$ such that (correctness) if $R(x,w)=1$ then $\mathsf{Dec}(\mathsf{Enc}(1^\lambda,x,m),w)=m$, and (soundness security) for every $x\notin L$, $\mathsf{Enc}(1^\lambda,x,0)\approx_c\mathsf{Enc}(1^\lambda,x,1)$ for efficient distinguishers, uniformly over $x$ chosen by the adversary. The statement $x$ acts as the public key and any witness as a decryption key. The scheme is **subexponentially secure** if for some constant $c>0$ distinguishers of size $2^{\lambda^{c}}$ have advantage at most $2^{-\lambda^{c}}$. Subexponentially secure witness encryption follows from subexponentially secure indistinguishability obfuscation, which Jain, Lin and Sahai built from well-founded assumptions.

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../../../security-games/semantic-security-and-indistinguishability/ind-secure.md)

## Sources

- Sanjam Garg, Craig Gentry, Amit Sahai, Brent Waters, "Witness Encryption and its Applications", STOC (2013), IACR ePrint 2013/258.
- Yizhi Huang, Rahul Ilango and Hanlin Ren, "NP-Hardness of Approximating Meta-Complexity: A Cryptographic Approach", STOC (2023), ECCC TR23-046.
