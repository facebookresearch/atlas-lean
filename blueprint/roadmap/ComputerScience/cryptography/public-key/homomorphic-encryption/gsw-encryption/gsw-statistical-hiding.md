# GSW ciphertexts are statistically hiding under a uniform public matrix

Let $A \in \mathbb{Z}_q^{m \times (n+1)}$ be uniform and visible to the adversary, $q = 2^w$. For an adversary that adaptively chooses messages and keeps arbitrary state, encryptions with independent binary coin matrices $R$ (rows $r_i \in \{0,1\}^m$) are close to a common ideal game in which each ciphertext is the decomposition of a uniform matrix: the acceptance probabilities in the two worlds differ by at most

$$
N\sqrt{2^{w(n+1)} / 2^m}
$$

per ciphertext. Adding a fixed message shift to a uniform matrix before decomposition preserves its law, so the ideal game does not depend on the messages.

## Proof sketch

Each row $r_i^{\mathsf T} A$ is a universal hash of $r_i$, so by the leftover hash lemma it is within $\tfrac12\sqrt{q^{n+1}/2^m}$ of uniform given $A$; there are $N$ independent rows per ciphertext.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)

## Proof depends on

- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
