# The spectrum drops strictly if no epoch grows and the oldest shrinks

Let `θ > 0`, let `n` and `i` be natural numbers with `1 ≤ i < n`, and let `t_k`, `t'_k`
(`k ∈ ℕ`) be real numbers with `t_k ≤ t'_k` for `2 ≤ k ≤ n` and `t_2 < t'_2`. Then the
[variable-size expected spectrum](../site-frequency-spectrum-under-variable-populatio/variable-sfs.md)
satisfies

`(θ / 2) ∑_{k=2}^{n} g_{n,i,k} t_k < (θ / 2) ∑_{k=2}^{n} g_{n,i,k} t'_k`,

with the [Griffiths–Tavaré kernel](../site-frequency-spectrum-under-variable-populatio/sfs-kernel.md)
`g_{n,i,k} = k C(n - i - 1, k - 2) / C(n - 1, k - 1)`. Replacing `t'` by `t` lengthens no mean
epoch and strictly shortens the oldest one (two lineages); it strictly lowers every entry
`1 ≤ i ≤ n - 1` of the expected spectrum.
