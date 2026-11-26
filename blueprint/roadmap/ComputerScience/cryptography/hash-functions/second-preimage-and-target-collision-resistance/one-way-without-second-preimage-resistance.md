# A one-way function need not be second-preimage resistant

If $h$ is one-way, then $h'(b \| m) = h(m)$ (ignoring one input bit) is one-way, but it is not second-preimage resistant: flipping the ignored bit gives a second preimage with probability $1$.

## Proof sketch

An inverter for $h'$ at length $n+1$ yields an inverter for $h$ at length $n$ by dropping the first bit of its output; the ignored bit is uniform and independent of the image.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
