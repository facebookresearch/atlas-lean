# Central limit theorem for independent clusters

**Central limit theorem for independent clusters** (Lindeberg form). Let `U k : Ω → E` be
independent, mean-zero, square-integrable cluster scores in a finite-dimensional real inner
product space. Suppose that for every direction `t`

* the averaged projected variances `n⁻¹ ∑_{k<n} E[⟪U k, t⟫²]` converge to `q t` (necessarily
  `q t ≥ 0`; `q t = 0` is allowed), and
* the projected triangular array `(√n)⁻¹ ⟪U k, t⟫`, `k < n`, satisfies the repository's
  Lindeberg condition `LindebergConditionTriangular`.

Then `(√n)⁻¹ • ∑_{k<n} U k` converges in distribution to any `Y` whose projections `⟪Y, t⟫` are
centered Gaussians of variance `q t`. The proof is Cramér–Wold plus the Lindeberg–Feller theorem
`lindeberg_feller_clt_triangular` applied to the cluster sums of each projection with `q t > 0`,
and Chebyshev's inequality for the projections with `q t = 0`.
