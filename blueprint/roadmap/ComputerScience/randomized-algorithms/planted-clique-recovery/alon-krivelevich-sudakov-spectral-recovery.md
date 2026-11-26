# Alon-Krivelevich-Sudakov: spectral recovery of a planted clique

**Algorithm A** of Alon, Krivelevich and Sudakov takes a unit eigenvector for the second largest eigenvalue of the ordinary adjacency matrix, selects the $k$ coordinates of largest absolute value, and applies degree cleanup. If $6 \le k$, $4096\,k \le n$ and $8192\sqrt{n} \le k$, then for every planted set $S$ of size $k$ it recovers $S$ with failure probability at most $2e^{-n} + n e^{-k/32}$, with no spectral-separation assumption.

## Depends on

- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)

## Proof depends on

- [Deterministic recovery from an approximate signal](planted-clique-deterministic-recovery.md)
- [Spectral norm of planted-clique noise is O(sqrt n)](../../../GraphTheory/random-graphs/planted-clique/planted-clique-noise-spectral-norm.md)
- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](../../../GraphTheory/random-graphs/planted-clique/planted-clique-outside-degrees.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
