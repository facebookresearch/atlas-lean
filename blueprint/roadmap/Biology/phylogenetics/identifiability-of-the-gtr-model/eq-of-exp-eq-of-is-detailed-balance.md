# Reversible generators are determined by one transition matrix

Let `ι` be a finite set of states. Let `π : ι → ℝ` have `π i > 0` for every `i`, and let `Q` and
`Q'` be real `ι × ι` matrices both in
[detailed balance](../../../Probability/markov-chains/finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/is-detailed-balance.md)
with `π`: `π i · Q i j = π j · Q j i`, and likewise for `Q'`. If `exp Q = exp Q'`, then `Q = Q'`.
Detailed balance matters: without it, distinct real matrices can have the same exponential, for
example `0` and `2π · [[0, 1], [-1, 0]]`.
