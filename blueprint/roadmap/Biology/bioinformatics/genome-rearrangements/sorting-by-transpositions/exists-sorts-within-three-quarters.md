# Odd-cycle upper bound on the transposition distance

**Odd-cycle upper bound on the transposition distance** (implied by Bafna–Pevzner 1998,
Corollary 6.10). Let `p` be a framed permutation of `1, …, n`: a list of length `n + 2` with
`WellFormed (p, 0)` (the bound `0` is not read). Then some number `m` of transpositions sorts `p`
(`SortingByTranspositionsFeasible (p, m)`) with `4m + 3 c_odd(p) ≤ 3(n + 1)`, that is
`m ≤ (3/4)(n + 1 - c_odd(p))`; with Theorem 2.4 this is within a factor `3/2` of `d(p)`.

## Sources

- V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240, Corollary 6.10.
- A. Labarre, *Combinatorial aspects of genome rearrangements and haplotype networks*, PhD thesis, Université libre de Bruxelles, 2008, Theorem 3.4, <https://theses.hal.science/tel-00482196v1>.
