# Security of an acyclic encrypted-key chain

Let $\mathcal{E}$ be IND-CPA secure with secret keys of length $\ell_{sk}$. Then the public acyclic key chain of depth $L$ is computationally indistinguishable from the chain in which every link encrypts the all-zero word: for every adversary $\mathcal{A}$ there is an adversary $\mathcal{B}$ against $\mathcal{E}$ with

$$
\bigl|\Pr[\mathcal{A}(\text{real chain}) = 1] - \Pr[\mathcal{A}(\text{zero chain}) = 1]\bigr| \le 2 L\, \ell_{sk} \cdot \mathrm{Adv}^{\mathrm{ind\text{-}cpa}}_{\mathcal{E}}(\mathcal{B}),
$$

and for polynomially bounded $L$ and $\ell_{sk}$ the difference is negligible. The hybrids replace links from the end of the chain and, within one link, bits from the beginning of the secret; the order matters because when link $i$ is replaced, $sk_{i+1}$ is no longer encrypted anywhere and can serve as the challenge key.

## Proof sketch

In the hybrid where links $i+1, \dots, L-1$ already encrypt zero, key $sk_{i+1}$ appears only through $pk_{i+1}$ and link $i$, so the reduction embeds its challenge public key as $pk_{i+1}$, generates all other keys itself, and splices the challenge ciphertext into link $i$; the bitwise-encryption hybrid handles each link.

## Depends on

- [Acyclic chains of encrypted secret keys](encrypted-key-chains.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [Bit-by-bit encryption of words is IND-CPA secure](bitwise-encryption-hybrid.md)
- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
