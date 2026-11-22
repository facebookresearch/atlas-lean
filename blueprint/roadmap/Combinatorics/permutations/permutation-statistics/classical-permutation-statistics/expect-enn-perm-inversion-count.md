# Expected number of inversions of a random permutation

Let $\sigma$ be a uniformly random permutation of $\{0, \dots, n-1\}$. The expected
[number of inversions](perm-inversion-count.md) of $\sigma$, computed in $[0, \infty]$, is

$$\mathbb{E}[\mathrm{inv}(\sigma)] = \frac{n(n - 1)}{4}.$$

Each of the $\binom{n}{2}$ pairs of positions is inverted with probability $1/2$; equivalently,
the expectation is the [total number of inversions](four-mul-sum-perm-inversion-count.md) divided
by $n!$. The expectation is taken in $[0, \infty]$, so no integrability side condition arises.

## Informally uses

- [Total number of inversions over all permutations](four-mul-sum-perm-inversion-count.md): the
  sum that is averaged.

## Background

- [Insertion sort](../../../../ComputerScience/sorting-and-searching/insertion-sort/README.md): by this result, straight insertion sort performs
  $n(n-1)/4$ exchanges on average, about $n^2/4$ and half of its worst case.
- [Expected number of hires is the harmonic number](../../../../ComputerScience/randomized-algorithms/hiring-problem/hire-assistant-expected-hires-to-real-eq.md):
  the companion average for random permutations, the expected number of
  [left-to-right maxima](perm-left-to-right-max-count.md), $H_n$.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Exercise 5.2-5 (the expected number of inversions of a uniform random
  permutation, by indicator random variables) and Problem 2-4 (inversions). The exercise asks for
  the value without stating it.
