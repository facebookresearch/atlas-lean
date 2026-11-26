# The extended pigeonhole formula needs width and clause space at least $n$

For all $m > n \ge 1$, every resolution refutation of $\mathrm{EPHP}^m_n$ has width at least $n$ and clause space at least $n$.

## Proof sketch

Duplicator survives the existential $n$-pebble game by maintaining a partial matching of the pebbled pigeons into distinct holes and setting extension variables consistently with it; this gives width at least $n$, and the space–width inequality with $k = 3$ gives space at least $n$.

## Depends on

- [The extended pigeonhole formula $\mathrm{EPHP}^m_n$](extended-pigeonhole-formula.md)
- [Clause space of resolution refutations](clause-space-of-resolution.md)

## Proof depends on

- [Atserias–Dalmau: the existential pebble game characterizes resolution width](atserias-dalmau-width-characterization.md)
- [Atserias–Dalmau inequality: clause space bounds width](clause-space-bounds-width.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008.
