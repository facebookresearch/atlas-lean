# Polynomial-time optimal sorting of signed permutations by reversals

For a signed permutation $\pi$ of $\{1, \dots, n\}$, Hannenhalli and Pevzner (1999, Theorem 6) give an algorithm, Reversal_Sort, that computes a sequence of $d(\pi)$ reversals transforming $\pi$ into the identity, where $d(\pi)$ is the reversal distance given by [the Hannenhalli–Pevzner formula](hannenhalli-pevzner-duality-theorem-for-signed-reversal-distance.md), and runs in $O(n^4)$ time. In particular a minimum sequence of reversals for a signed permutation is computable in polynomial time.

## Depends on

- [Hannenhalli–Pevzner formula for the signed reversal distance](hannenhalli-pevzner-duality-theorem-for-signed-reversal-distance.md)

## Expansion

1. The breakpoint graph, cycles, hurdles and fortresses, and the value of the formula, maintained along the algorithm.
2. Safe reversals in oriented components and hurdle merging and cutting, each decreasing the formula by exactly $1$ (Theorems 2–4 and Lemmas 14–21).
3. The running time bound of Theorem 6.

## Sources

- S. Hannenhalli and P. A. Pevzner, Transforming cabbage into turnip: polynomial algorithm for sorting signed permutations by reversals, J. ACM 46 (1999), 1–27, Theorem 6. <https://doi.org/10.1145/300515.300516>
