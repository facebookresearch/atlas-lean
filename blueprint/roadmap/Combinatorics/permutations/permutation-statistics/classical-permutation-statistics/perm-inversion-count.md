# Number of inversions of a permutation

$\mathrm{inv}(\sigma)$ is the number of [inversions](perm-inversions.md) of the permutation
$\sigma$ of $\{0, \dots, n-1\}$: the number of pairs of positions $i < j$ with
$\sigma(j) < \sigma(i)$. It is $0$ for the identity and $n(n-1)/2$ for the reversal.

## Background

- [Insertion sort](../../../../ComputerScience/sorting-and-searching/insertion-sort/README.md): straight insertion moves each element left past exactly
  the earlier elements that form an inversion with it, so $\mathrm{inv}(\sigma)$ measures its
  work.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Exercise 5.2-5 (the expected number of inversions of a uniform random
  permutation, by indicator random variables) and Problem 2-4 (inversions). The exercise asks for
  the value without stating it.
