# One step of the method of steps

For real numbers `r`, `K` and `τ` and functions `ψ, x : ℝ → ℝ`, the step map sends `x` to the
function equal to `ψ(t)` for `t ≤ 0` and to `ψ(0) exp(r ∫₀ᵗ (1 - x(s - τ) / K) ds)` for `t > 0`.
With the conventions `a / 0 = 0` and that the integral of a non-integrable function is `0`, it is
defined for all inputs. For `τ ≥ 0` its value on `[0, τ]` uses `x` only on `[-τ, 0]`, and by the
[integral representation](eq-mul-exp-integral.md) a [solution](is-solution.md) `x` with history
`ψ` agrees with its image on `[-τ, ∞)`.
