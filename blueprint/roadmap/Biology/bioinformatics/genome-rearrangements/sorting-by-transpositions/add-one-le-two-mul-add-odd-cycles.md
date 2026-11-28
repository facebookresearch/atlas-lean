# Odd-cycle lower bound

**Odd-cycle lower bound** (Bafna–Pevzner 1998, Theorem 2.4). Let `p` be a framed
permutation of `1, …, n`: a list of length `n + 2` that `WellFormed (p, m)` makes a permutation
of `[0, 1, …, n + 1]` with first entry `0` and last entry `n + 1`. If at most `m`
transpositions sort `p` (`SortingByTranspositionsFeasible (p, m)`), then
`n + 1 ≤ 2m + c_odd(p)`; that is, `d(p) ≥ (n + 1 - c_odd(p))/2`.

## Sources

- V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240, Theorem 2.4.
- A. Labarre, *Combinatorial aspects of genome rearrangements and haplotype networks*, PhD thesis, Université libre de Bruxelles, 2008, Theorem 3.1, <https://theses.hal.science/tel-00482196v1>.
