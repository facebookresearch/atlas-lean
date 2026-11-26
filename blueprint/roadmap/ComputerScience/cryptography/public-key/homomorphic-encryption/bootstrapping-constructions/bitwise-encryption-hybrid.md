# Bit-by-bit encryption of words is IND-CPA secure

Let $\mathcal{E}$ be an IND-CPA secure bit-encryption scheme and encrypt a word $x \in \{0,1\}^\ell$ by encrypting each bit independently under the same public key. For every adversary $\mathcal{A}$ distinguishing encryptions of two adaptively chosen words of length $\ell$ there is an adversary $\mathcal{B}$ against $\mathcal{E}$ whose running time exceeds that of $\mathcal{A}$ by at most the time of $\ell$ encryptions under $\mathcal{E}$ such that

$$
\mathrm{Adv}(\mathcal{A}) \le 2\ell \cdot \mathrm{Adv}^{\mathrm{ind\text{-}cpa}}_{\mathcal{E}}(\mathcal{B}).
$$

The $j$-th hybrid replaces the first $j$ bits of the word by zeros; $\mathcal{B}$ picks $j$ at random, samples the other ciphertexts itself and inserts its challenge ciphertext at coordinate $j$, which is an encryption of the original bit or of zero according to the challenge bit.

## Proof sketch

Adjacent hybrids differ in one coordinate, and the challenge splice realizes either hybrid exactly; average over the random coordinate and apply the hybrid argument on both words.

## Depends on

- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)

## Proof depends on

- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
