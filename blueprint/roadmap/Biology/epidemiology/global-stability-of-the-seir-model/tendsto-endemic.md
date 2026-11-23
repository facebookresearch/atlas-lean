# Global attractivity of the endemic equilibrium

If `σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0`
and `R₀ = β σ / ((μ + σ) (μ + γ)) > 1`, every solution starting in the open positive orthant
(`S(0), E(0), I(0) > 0`) converges to `(S*, E*, I*)`.

The invariance step, done along the trajectory: `V̇ ≤ -μ (S - S*)² / S` and `V` converges, so
by Barbalat's lemma `S → S*`; then Barbalat for `S` gives `S' → 0`, i.e. `I → I*`; and for `I`
it gives `I' → 0`, i.e. `E → E*`. This is the statement that the only trajectory inside the
zero set of `V̇` (`lyapunovDeriv_eq_zero_iff`) is the equilibrium.
