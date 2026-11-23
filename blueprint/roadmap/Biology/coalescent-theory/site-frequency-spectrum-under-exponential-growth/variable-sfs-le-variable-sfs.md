# The variable-size spectrum is monotone in the mean holding times

Let `θ ≥ 0`, let `n` be a natural number and let `t_k`, `t'_k` (`k ∈ ℕ`) be real numbers with
`t_k ≤ t'_k` for `2 ≤ k ≤ n`. Then for every natural number `i` the
[variable-size expected spectrum](../site-frequency-spectrum-under-variable-populatio/variable-sfs.md)
satisfies

`(θ / 2) ∑_{k=2}^{n} g_{n,i,k} t_k ≤ (θ / 2) ∑_{k=2}^{n} g_{n,i,k} t'_k`,

with the [Griffiths–Tavaré kernel](../site-frequency-spectrum-under-variable-populatio/sfs-kernel.md)
`g_{n,i,k} = k C(n - i - 1, k - 2) / C(n - 1, k - 1)`, defined at all indices with natural
subtractions truncated at `0` and division by `0` giving `0`, and nonnegative there. In the sums
`2 ≤ k ≤ n`, so `C(n - 1, k - 1) > 0` and no division by `0` occurs; as `i` is unrestricted, the
subtraction `n - i - 1` is truncated at `0` when `i ≥ n`. The inequality holds for every natural
number `i`, including `i ≥ n`, and for real `t_k`, `t'_k` of any sign (for example `t_2 = -1`).
It compares expected spectra when `1 ≤ i ≤ n - 1` and `t_k`, `t'_k` are mean holding times, hence
nonnegative.
