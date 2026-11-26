# At bounded compression, second-preimage resistance does not imply one-wayness

Let $H$ be second-preimage resistant and $k \ge 1$ a constant. Define $H'(w) = 1 \| w_{k+1..}$ if the first $k$ bits of $w$ are all zero, and $H'(w) = 0 \| H(w)$ otherwise. Then $H'$ is second-preimage resistant, but the inverter that answers $0^k$ followed by the tail of its challenge inverts $H'$ with probability at least $2^{-k}$, so $H'$ is not one-way.

## Proof sketch

On the planted branch $H'$ is injective, so a uniform input there has no second preimage; off it, a second preimage for $H'$ is one for $H$. The inverter succeeds whenever the input fell in the planted branch.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
