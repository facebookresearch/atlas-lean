# The variable-size spectrum is monotone in the mean holding times

Let `θ ≥ 0`, let `n` be a natural number and let `t_k`, `t'_k` (`k ∈ ℕ`) be real numbers with
`t_k ≤ t'_k` for `2 ≤ k ≤ n`. Then for every natural number `i` the
[variable-size expected spectrum](../site-frequency-spectrum-under-variable-populatio/variable-sfs.md)
satisfies

`(θ / 2) ∑_{k=2}^{n} g_{n,i,k} t_k ≤ (θ / 2) ∑_{k=2}^{n} g_{n,i,k} t'_k`,

with the [Griffiths–Tavaré kernel](../site-frequency-spectrum-under-variable-populatio/sfs-kernel.md)
`g_{n,i,k} = k C(n - i - 1, k - 2) / C(n - 1, k - 1)` (subtractions truncated at `0`, division
by `0` giving `0`), which is nonnegative for all indices.
