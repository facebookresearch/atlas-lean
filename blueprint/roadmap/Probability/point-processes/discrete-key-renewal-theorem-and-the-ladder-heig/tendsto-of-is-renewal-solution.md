# Discrete key renewal theorem

Assume `f 0 = 0`, `HasSum f 1`, `HasSum (fun k : ℕ => (k : ℝ) * f k) μ` and `IsRenewalSolution f z Z`.

For an aperiodic interarrival law `f` on `{1, 2, …}`
with finite mean `μ` and a summable forcing `z`, every solution of the renewal equation
`Z n = z n + ∑_{k ≤ n} f k * Z (n - k)` converges to `(∑ z) / μ`.
