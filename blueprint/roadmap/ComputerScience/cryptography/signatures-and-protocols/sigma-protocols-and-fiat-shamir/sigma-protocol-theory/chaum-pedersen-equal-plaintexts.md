# Chaum–Pedersen proofs of equal ElGamal plaintexts

Let $\mathbb{G}$ have prime order $q$ and generator $g$, written additively, and let $u = \alpha g$ be an ElGamal public key. Two multiplicative-ElGamal ciphertexts $(v_0, e_0) = (\beta_0 g, \beta_0 u + m_0)$ and $(v_1, e_1) = (\beta_1 g, \beta_1 u + m_1)$ encrypt the same plaintext iff $(v_0 - v_1, e_0 - e_1) = \beta(g, u)$ for $\beta = \beta_0 - \beta_1$, i.e. iff the pair is a Diffie–Hellman tuple relative to $(g, u)$. The Chaum–Pedersen Sigma protocol for equality of discrete logarithms, applied to this pair through a language reduction, is complete and special HVZK, and it is sound with error at most $1/q$ against arbitrary provers: if the plaintexts differ, no prover makes the verifier accept with probability more than $1/q$.

## Proof sketch

Equality of plaintexts is equivalent to the difference pair lying in the line spanned by $(g, u)$; the generic linear protocol for $\psi(\beta) = (\beta g, \beta u)$ is special sound, so the language-reduction theorem gives soundness error $1/|C| = 1/q$.

## Depends on

- [The generic linear Sigma protocol](generic-linear-sigma-protocol.md)
- [ElGamal as a public-key encryption scheme](../../../public-key/cpa-security-of-elgamal/scheme.md)

## Proof depends on

- [Completeness, special soundness, HVZK and unique responses of linear Sigma protocols](linear-sigma-protocol-properties.md)
- [Language reductions transfer soundness of Sigma protocols](sigma-language-reductions.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
