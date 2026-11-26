# Completeness, special soundness, HVZK and unique responses of linear Sigma protocols

For the generic linear Sigma protocol over prime $q$: honest conversations are accepting; the extractor $x = (z - z')/(c - c')$ is a witness extractor; the simulator that samples $z$ uniformly and sets $t = \psi_y(z) - c\,w_y$ is a perfect simulator at every challenge (special HVZK). The protocol has unique responses at $y$ exactly when $\psi_y$ is injective (its homogeneous system has only the zero solution); in particular Schnorr's protocol (when $r \mapsto r g$ is injective) and Chaum–Pedersen have unique responses, and with special soundness, unique responses give strong special soundness with the same extractor. Applied to two ElGamal ciphertexts under one public key, the Chaum–Pedersen instance proves equality of plaintexts with soundness error $1/q$ against arbitrary provers.

## Proof sketch

Linearity gives $\psi_y(z - z') = (c - c') w_y$. Unique responses: two responses to the same $(t, c)$ differ by an element of $\ker \psi_y$. Strong special soundness: if $c = c'$ then unique responses force $z = z'$, so $(c, z) \ne (c', z')$ implies $c \ne c'$.

## Depends on

- [The generic linear Sigma protocol](generic-linear-sigma-protocol.md)
- [Efficient special soundness, efficient special HVZK and computational special HVZK](efficient-sigma-protocol-notions.md)

## Proof depends on

- [Language reductions transfer soundness of Sigma protocols](sigma-language-reductions.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
