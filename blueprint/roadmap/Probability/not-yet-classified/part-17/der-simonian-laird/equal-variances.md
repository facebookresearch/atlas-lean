# Equal sampling variances

Let `k ≥ 2` and let every
sampling variance equal `s² > 0`. For real study estimates `y`, with `ȳ = ∑ y_i / k`: the
DerSimonian–Laird estimator is `max {0, ∑ (y_i - ȳ)² / (k - 1) - s²}`, and for every `Δ² ≥ 0`
the random-effects pooled estimate is `ȳ` with `(∑ᵢ (s² + Δ²)⁻¹)⁻¹ = (s² + Δ²) / k`.

## Sources

- R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7 (1986) 177–188, p. 183.
