# Time-weighted block-count moment at level $k$

For natural numbers `n`, `k`, `i` and `j`, let `J` be the
[transition operator of random joining](../expected-site-frequency-spectrum/join-step.md), `1ⁿ` the list of `n` ones and
`c_i(y)` the number of entries of a list `y` equal to `i`. The level moment is

`M_n(k; i, j) = ∑_{l=2}^{k} C(l, 2)⁻¹ J^{n-k}(y ↦ c_i(y) (J^{(n-l)-(n-k)} c_j)(y))(1ⁿ)`,

with natural-number subtraction truncated at `0`. The intended domain is `2 ≤ k ≤ n`. There the
exponent `(n - l) - (n - k)` is `k - l`, and by the
[two-level Markov property of random joining](../branch-length-covariances-from-random-joining/exists-finset-random-joining-pair.md) the
summand is `C(l, 2)⁻¹ E[c_{k,i} c_{l,j}]`, where `c_{k,i}` is the number of blocks of size `i`
while `k` lineages remain under random joining from `n` singletons and `1 / C(l, 2)` is the mean
holding time of Kingman's coalescent with `l` lineages. For `k > n` the truncation `n - k = 0`
gives instead `M_n(k; i, j) = c_i(1ⁿ) ∑_{l=2}^{k} C(l, 2)⁻¹ (J^{n-l} c_j)(1ⁿ)`, where `c_i(1ⁿ)` is
`n` if `i = 1` and `0` otherwise. For `k = 0` or `k = 1` the sum over `2 ≤ l ≤ k` is empty and
`M_n(k; i, j) = 0` for all `n`, `i` and `j`.
