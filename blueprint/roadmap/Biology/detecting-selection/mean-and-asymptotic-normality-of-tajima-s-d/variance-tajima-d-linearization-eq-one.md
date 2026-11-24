# Unit delta-method variance of Tajima's D under neutral-model moments

Let `μ` be a probability measure, `n ≥ 4`, `θ > 0`, and let `T_k` be
[Kingman holding times](../../coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of `n` genes under `μ` (mutually independent, with `T_k` exponential of rate
`k (k - 1) / 2` for `2 ≤ k ≤ n`), with
[total branch length](../../coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/total-length.md)
`L`. Let `𝒢` be a sub-σ-algebra and, for all
[pairs](../../coalescent-theory/segregating-sites-and-pairwise-differences/sample-pairs.md) `s, t`
of genes, let `τ_s` (pairwise coalescence times), `ℓ_{st}` (shared branch lengths), `D_s`
(pairwise differences) and `S` (segregating sites) be real random variables such that:

- `S` is square integrable, with `E[S | 𝒢] = Var(S | 𝒢) = (θ / 2) L` almost surely;
- each `τ_s` is exponential with rate `1`; `E[τ_s τ_t] = 4/3` when `s` and `t` share exactly one
  gene and `11/9` when they are disjoint; `E[τ_s L] = 2 a₁ + (n + 2) / n`;
- `ℓ_{ss} = 2 τ_s` almost surely; `ℓ_{st} = τ_s + τ_t - τ_{s △ t}` almost surely when `s` and `t`
  share exactly one gene; `E[ℓ_{st}] = 2/3` when they are disjoint;
- each `D_s` is square integrable, and almost surely `E[D_s | 𝒢] = θ τ_s`,
  `E[D_s D_t | 𝒢] = θ² τ_s τ_t + (θ / 2) ℓ_{st}` and `E[D_s S | 𝒢] = (θ² / 2) τ_s L + θ τ_s`.

Let `N = π - S / a₁`, with `π` the
[mean number of pairwise differences](../../coalescent-theory/segregating-sites-and-pairwise-differences/mean-pair-diff.md)
of the `D_s`, `V = e₁ S + e₂ S (S - 1)` and `v = c₁ θ + c₂ θ²`. Then the map `(x, y) ↦ x / √y`
has derivative `(dx, dy) ↦ dx / √v` at the mean point `(E N, E V)`, which is `(0, v)`, and the
linearization `(N - E N) / √v` of [Tajima's D](../tajima-s-d/tajima-d.md), this derivative
applied to `(N - E N, V - E V)`, has variance `1`.
