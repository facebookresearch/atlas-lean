# Tendsto det div prod sub of injective

Let `f_0, …, f_{g-1}` be functions `ℂ → ℂ` that are holomorphic on a set `U` which is a
neighbourhood of `a`. Then, as `z = (z_0, …, z_{g-1})` tends to `(a, …, a)` through tuples of
pairwise distinct complex numbers (`Function.Injective z`),
`det (f_k(z_l))_{k,l} / ∏_{k<l} (z_l - z_k) → det (f_k^{(l)}(a) / l!)_{k,l}`,
where `f^{(l)} = iteratedDeriv l f` and the indices `k, l` run over `Fin g` (so `l` here is the
`l - 1` of de Jong's 1-based indexing). The points `z_l` are not required to lie in `U`, and
`g = 0` is allowed (both sides are then `1`). This is a slightly stronger form of
`Complex.tendsto_det_div_prod_sub`.
