# Greedy sorting uses at most twice the reversal distance

For every unsigned permutation `π` of `1, …, n` and every greedy run `rs` from `π`, `|rs| ≤ 2 d(π)`,
where `d(π)` is the unsigned reversal distance of `π`: the greedy breakpoint algorithm uses at most
twice the least number of reversals that sort `π` (implied by Kececioglu–Sankoff 1995, Corollary 1).

The source derives it from Theorem 1, which bounds every greedy run by the number `φ(π)` of
breakpoints, and from `φ(π) ≤ 2 d(π)`, since a reversal removes at most two breakpoints.

## Depends on

- [Greedy Run](greedy-run.md)
- [Permutation of 1, …, n as a list of integers](../../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/uvalid.md)
- [Unsigned reversal distance of a permutation of 1, …, n](../../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/udist.md)

## Proof depends on

- [The greedy algorithm sorts within `φ(π)` reversals](greedy-run-length-le-and-sorts.md)
- [Unsigned breakpoints are at most twice the unsigned reversal distance](../../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/ub-le-two-mul-udist.md)

## Sources

- J. Kececioglu and D. Sankoff, "Exact and approximation algorithms for sorting by reversals, with
  application to genome rearrangement", Algorithmica 13 (1995) 180-210, Corollary 1.
