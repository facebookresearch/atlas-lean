# Almost-sure concentration of the Gamma laws at pooled counts

Let `μ` be a probability measure, `a > 0`, `b > 0`, `r₀ ≥ 0` and `B, C` real numbers. Let
`s₀, s₁, …` be real numbers with `sᵢ ≤ B` and `Sₙ = ∑_{i<n} sᵢ → ∞`, and let `X₀, X₁, …` be random
variables with values in `ℕ` that are pairwise independent and square-integrable, with
`E Xᵢ = sᵢ r₀` and `Var Xᵢ ≤ C sᵢ`. Write `Kₙ = ∑_{i<n} Xᵢ`. Then almost surely
`(a + Kₙ) / (b + Sₙ) → r₀`, `(a + Kₙ) / (b + Sₙ)² → 0`, and the mass that `Gamma(a + Kₙ, b + Sₙ)`
assigns to `{x : |x − r₀| ≥ ε}`, outside the neighbourhood `(r₀ − ε, r₀ + ε)`, tends to `0` for
every `ε > 0`.

No sign condition on `sᵢ` is imposed (for `r₀ > 0`, `sᵢ ≥ 0` follows from `E Xᵢ = sᵢ r₀ ≥ 0`), so
`b + Sₙ` may be nonpositive for small `n`. There `Gamma(a + Kₙ, b + Sₙ)` is the measure whose
density is the Gamma formula with negative values replaced by `0`; it is not a probability law, and
these laws need not be posteriors. For nonnegative exposures they are the pooled posteriors: see
[the theorem with exposures](ae-tendsto-pooled-posterior-exposures.md). The counts are not
identically distributed: the ratio `Kₙ / Sₙ → r₀` comes from a strong law of large numbers for
nonnegative variables that are not identically distributed.
