# Completeness, special soundness and special HVZK of linear Sigma protocols

For the generic linear Sigma protocol over prime $q$: honest conversations are accepting; the extractor $x = (z - z')/(c - c')$ is a witness extractor; the simulator that samples $z$ uniformly and sets $t = \psi_y(z) - c\,w_y$ is a perfect simulator at every challenge (special HVZK).

## Proof sketch

Linearity gives $\psi_y(z - z') = (c - c') w_y$, and $c - c'$ is invertible modulo the prime $q$. For the simulator, $\psi_y(z) - c\,w_y$ with uniform $z$ has the distribution of an honest commitment, and the verification equation holds by construction.

## Depends on

- [The generic linear Sigma protocol](generic-linear-sigma-protocol.md)
- [Efficient special soundness, efficient special HVZK and computational special HVZK](efficient-sigma-protocol-notions.md)

## Sources

- Ueli Maurer, "Unifying Zero-Knowledge Proofs of Knowledge", Progress in Cryptology – AFRICACRYPT 2009, LNCS 5580, Springer, 2009, pp. 272–286, Theorem 3.
- Ronald Cramer, Ivan Damgård and Berry Schoenmakers, "Proofs of Partial Knowledge and Simplified Design of Witness Hiding Protocols", Advances in Cryptology – CRYPTO '94, LNCS 839, Springer, 1994, pp. 174–187, Section 2.
