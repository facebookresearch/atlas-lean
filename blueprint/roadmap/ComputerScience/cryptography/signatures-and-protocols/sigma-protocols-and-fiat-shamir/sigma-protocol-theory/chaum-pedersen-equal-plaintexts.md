# Chaum–Pedersen proofs of equal ElGamal plaintexts

Let $\mathbb{G}$ have prime order $q$ and generator $g$, written additively, and let $u = \alpha g$ be an ElGamal public key. Two multiplicative-ElGamal ciphertexts $(v_0, e_0) = (\beta_0 g, \beta_0 u + m_0)$ and $(v_1, e_1) = (\beta_1 g, \beta_1 u + m_1)$ encrypt the same plaintext iff $(v_0 - v_1, e_0 - e_1) = \beta(g, u)$ for $\beta = \beta_0 - \beta_1$, i.e. iff the pair is a Diffie–Hellman tuple relative to $(g, u)$. The Chaum–Pedersen Sigma protocol for equality of discrete logarithms, run on the difference pair $(v_0 - v_1, e_0 - e_1)$ relative to $(g, u)$, is complete and special HVZK, and it is sound with error at most $1/q$ against arbitrary provers: if the plaintexts differ, no prover makes the verifier accept with probability more than $1/q$.

## Proof sketch

Equality of plaintexts is equivalent to the difference pair lying in the line spanned by $(g, u)$; the generic linear protocol for $\psi(\beta) = (\beta g, \beta u)$ is special sound and special HVZK, and a special-sound three-move protocol with challenge set $C = \mathbb{Z}_q$ is knowledge sound with knowledge error $1/|C| = 1/q$; on a false statement no witness exists, so the acceptance probability is at most $1/q$.

## Depends on

- [The generic linear Sigma protocol](generic-linear-sigma-protocol.md)
- [ElGamal as a public-key encryption scheme](../../../public-key/cpa-security-of-elgamal/scheme.md)

## Proof depends on

- [Completeness, special soundness and special HVZK of linear Sigma protocols](linear-sigma-protocol-properties.md)

## Sources

- David Chaum and Torben Pryds Pedersen, "Wallet Databases with Observers", Advances in Cryptology – CRYPTO '92, LNCS 740, Springer, 1993, pp. 89–105, Section 3.2.
- Ueli Maurer, "Unifying Zero-Knowledge Proofs of Knowledge", Progress in Cryptology – AFRICACRYPT 2009, LNCS 5580, Springer, 2009, pp. 272–286, Theorem 3.
- Thomas Attema, Ronald Cramer and Lisa Kohl, "A Compressed Σ-Protocol Theory for Lattices", Advances in Cryptology – CRYPTO 2021, Springer, 2021, Corollary 1.
