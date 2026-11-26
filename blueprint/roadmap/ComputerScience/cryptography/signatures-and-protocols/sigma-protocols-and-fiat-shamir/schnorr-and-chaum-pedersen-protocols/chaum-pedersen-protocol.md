# The Chaum–Pedersen protocol for Diffie–Hellman triples

In a group of prime order $q$ with generator $g$, the *Chaum–Pedersen* protocol proves that $(u, v, w)$ is a Diffie–Hellman triple with witness $\beta$, $v = g^{\beta}$ and $w = u^{\beta}$: the prover sends $(t_1, t_2) = (g^{r}, u^{r})$, receives $c \in \mathbb{Z}_q$, replies $z = r + c\beta$, and the verifier checks $g^{z} = t_1 v^{c}$ and $u^{z} = t_2 w^{c}$. It is complete, efficiently special sound, and special HVZK (statistically, with error $2 \cdot 2^{-n}$ for fair-coin nonces), with polynomial-time prover, verifier, extractor and simulator.

## Proof sketch

It is the linear Sigma protocol for the homomorphism $\beta \mapsto (g^\beta, u^\beta)$.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Real DDH experiment](../../../public-key/elgamal-encryption/ddh-real.md)

## Proof depends on

- [Linear Sigma protocols are complete, special sound and special HVZK](linear-sigma-protocols.md)

## Sources

- D. Chaum and T. P. Pedersen, "Wallet Databases with Observers", Advances in Cryptology (CRYPTO 1992), LNCS 740, 1993.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
