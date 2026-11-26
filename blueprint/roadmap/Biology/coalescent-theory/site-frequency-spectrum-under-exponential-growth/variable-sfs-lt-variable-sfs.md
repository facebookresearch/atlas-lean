# For θ > 0 the SFS falls if no epoch grows and the oldest shortens

Let `θ > 0`, let `n` and `i` be natural numbers with `1 ≤ i < n`, and let `t_k`, `t'_k`
(`k ∈ ℕ`) be real numbers with `t_k ≤ t'_k` for `2 ≤ k ≤ n` and `t_2 < t'_2`. Then the
[variable-size expected spectrum](../site-frequency-spectrum-under-variable-populatio/variable-sfs.md)
satisfies

`(θ / 2) ∑_{k=2}^{n} g_{n,i,k} t_k < (θ / 2) ∑_{k=2}^{n} g_{n,i,k} t'_k`,

with the [Griffiths–Tavaré kernel](../site-frequency-spectrum-under-variable-populatio/sfs-kernel.md)
`g_{n,i,k} = k C(n - i - 1, k - 2) / C(n - 1, k - 1)`; for `1 ≤ i < n` and `2 ≤ k ≤ n` no
subtraction is truncated and `C(n - 1, k - 1) > 0`. The inequality holds for real `t_k`, `t'_k`
of any sign. When they are mean holding times, hence nonnegative, replacing `t'` by `t`
lengthens no mean epoch (`t_k ≤ t'_k` for every `2 ≤ k ≤ n`) and strictly shortens the oldest
one, with two lineages (`t_2 < t'_2`); this strictly lowers every entry `1 ≤ i ≤ n - 1` of the
expected spectrum.
