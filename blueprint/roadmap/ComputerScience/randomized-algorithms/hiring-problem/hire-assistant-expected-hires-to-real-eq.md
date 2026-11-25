# Expected number of hires is the harmonic number

Let $x$ be a list of $n$ pairwise
distinct elements of a linearly ordered type, and rearrange its entries by a uniformly random
permutation of the indices. The expected number of hires that the hire-assistant procedure
(interview the entries in order, hiring each one strictly better than every earlier one) makes
on the rearranged list, an element of $[0, \infty]$, converted to a real number, equals the
harmonic number $H_n = \sum_{k=1}^{n} \frac{1}{k}$.

## Background

- [Number of left-to-right maxima](../../../Combinatorics/permutations/permutation-statistics/classical-permutation-statistics/perm-left-to-right-max-count.md):
  the hires are the left-to-right maxima (records) of the interview order, so this is the
  expected number of left-to-right maxima of a random permutation.
- [Expected number of inversions of a random permutation](../../../Combinatorics/permutations/permutation-statistics/classical-permutation-statistics/expect-enn-perm-inversion-count.md):
  the companion average over random permutations, $n(n-1)/4$.
