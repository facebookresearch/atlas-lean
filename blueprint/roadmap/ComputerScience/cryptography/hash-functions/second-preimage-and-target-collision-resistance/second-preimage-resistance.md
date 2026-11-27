# Second-preimage resistance

A polynomial-time function $H$ mapping $n$-bit inputs to $\mathrm{out}(n)$-bit digests is *second-preimage resistant* if every probabilistic polynomial-time adversary, given $1^n$ and a uniform $m \in \{0,1\}^n$, outputs $m' \ne m$ with $H(m') = H(m)$ only with negligible probability. Collision resistance implies second-preimage resistance.

## Depends on

- [Collision resistance and target collision resistance](../collision-resistance-and-target-collision-resistance.md)
- [Negligible functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/negligible.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
