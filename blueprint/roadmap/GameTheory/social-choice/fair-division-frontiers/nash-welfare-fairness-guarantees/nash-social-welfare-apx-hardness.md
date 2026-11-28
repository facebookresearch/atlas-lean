# Maximum Nash social welfare is APX-hard for additive valuations

There is a constant $c > 1$ (one can take $c \approx 1.00008$) such that, unless $\mathrm{P} = \mathrm{NP}$, no polynomial-time algorithm is a $c$-approximation for maximum Nash social welfare on instances with additive valuations. In particular maximum Nash social welfare admits no polynomial-time approximation scheme unless $\mathrm{P} = \mathrm{NP}$.

## Proof sketch

Reduce from vertex cover in $3$-regular graphs, for which it is NP-hard to distinguish graphs with a small vertex cover from graphs whose vertex covers are all larger by a constant factor. Each vertex becomes a vertex agent with vertex items and each edge becomes an edge agent sharing items with the agents of its endpoints; an exchange argument shows some optimal allocation has a canonical form in which vertex agents keep at most one vertex item. Small vertex covers then correspond to allocations giving every agent value close to a target, while in the other case a constant fraction of agents lose a constant factor of value, which lowers the geometric mean by a constant factor.

## Depends on

- [Approximation ratio for the Nash social welfare objective](nash-social-welfare-approximation-ratio.md)

## Sources

- E. Lee, "APX-hardness of maximizing Nash social welfare with indivisible items", Information Processing Letters 122 (2017).
