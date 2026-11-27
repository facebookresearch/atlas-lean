# Security of the accumulator under strong RSA

Under the strong RSA assumption, no efficient adversary outputs an accumulator value $c$, an element $x$ with $H(x) \ne \pm 1$, a membership proof $a$ and a non-membership proof $(b, \gamma)$ that both verify, except with negligible probability. Accumulated sets therefore cannot be equivocated.

## Proof sketch

From $a^{H(x)} = c$ and $c^{\gamma} b^{H(x)} = g$ one obtains $(b\, a^{\gamma})^{H(x)} = g$, a strong RSA solution with exponent $H(x)$.

## Depends on

- [Accumulator in a group of unknown order](accumulator-group-of-unknown-order.md)

## Sources

- J. Li, N. Li and R. Xue, "Universal Accumulators with Efficient Nonmembership Proofs", Applied Cryptography and Network Security (ACNS 2007), LNCS 4521, 2007.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
