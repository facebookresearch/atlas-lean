# Variance of Tajima's `D` numerator from the SFS

**Variance of Tajima's `D` numerator from the SFS** (Tajima 1989, `n ≥ 2`):
`Var(θ_π - S / a₁) = c₁ θ + (θ / 2)² Var(∑_i w_i L_i)` with
`w_i = i (n - i) / C(n, 2) - 1 / a₁` (`tajimaNumWeight`). The `θ`-linear coefficient is
Tajima's `c₁` (`sum_tajimaNumWeight_sq_div`); the `θ²` coefficient needs exactly the
covariances `Cov(L_i, L_j)` weighted by `w_i w_j` (`variance_sum_eq_sum_covariance`), i.e. the
combination that Tajima's `c₂` evaluates (Tajima 1989; not proved here).
