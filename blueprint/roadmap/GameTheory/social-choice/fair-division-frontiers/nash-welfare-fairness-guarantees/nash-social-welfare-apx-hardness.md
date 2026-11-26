# Maximum Nash social welfare is APX-hard for additive valuations

There is a constant $c > 1$ such that, unless $\mathrm{P} = \mathrm{NP}$, no polynomial-time algorithm is a $c$-approximation for maximum Nash social welfare on instances with additive valuations. In particular maximum Nash social welfare admits no polynomial-time approximation scheme unless $\mathrm{P} = \mathrm{NP}$.

## Proof sketch

Reduce from a bounded-occurrence gap version of a constraint satisfaction problem (for instance a gap version of 3-dimensional matching). Each constraint becomes a group of goods valued by a few agents; satisfying assignments correspond to allocations giving every agent value close to a target, while in the soft case a constant fraction of agents necessarily lose a constant factor of value, which lowers the geometric mean by a constant factor.

## Depends on

- [Approximation ratio for the Nash social welfare objective](nash-social-welfare-approximation-ratio.md)

## Sources

- E. Lee, "APX-hardness of maximizing Nash social welfare with indivisible items", Information Processing Letters 122 (2017).
