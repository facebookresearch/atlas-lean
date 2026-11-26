# Planted clique recovery above every constant multiple of sqrt n

For every fixed $c > 0$ there is a single polynomial-time algorithm that, given the graph and the target size $k$, recovers the planted clique with probability tending to $1$ whenever $k(n) \ge c\sqrt{n}$ for all large $n$, for arbitrary priors on planted sets of the given sizes. The algorithm enumerates all vertex lists of a fixed size $s = s(c)$, restricts the graph to their common neighbourhood, runs the spectral base algorithm on it with the reduced target size, lifts the output, and returns the first candidate verified to be a clique of size $k$.

## Proof sketch

For a seed inside $S$, the common neighbourhood keeps all of $S$ minus the seed but only about $n/2^s$ outsiders, so the reduced clique is above the base algorithm's threshold $1024\sqrt{n'}$; an exposure coupling transfers the base failure bound, Hoeffding controls the neighbourhood size, and uniqueness of the planted clique makes the first verified candidate correct.

## Depends on

- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Planted clique recovery by exact integer matrix powers](integer-matrix-power-recovery.md)
- [Alon-Krivelevich-Sudakov: spectral recovery of a planted clique](alon-krivelevich-sudakov-spectral-recovery.md)
- [Two-sided Hoeffding inequality for Bernoulli sums](../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
