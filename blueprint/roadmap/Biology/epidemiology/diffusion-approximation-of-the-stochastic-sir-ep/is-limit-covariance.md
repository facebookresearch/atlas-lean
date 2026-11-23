# Is Limit Covariance

`V = (V₁₁, V₁₂, V₂₂)` is the **limit covariance** of the SIR diffusion approximation around
`x`, started from `V₀`: it solves the Lyapunov equation `V' = DF(x) V + V DF(x)ᵀ + G(x)`
(`lyapunovField`, written out in `lyapunovField_apply`) for `t ≥ 0`, with `V(0) = V₀`. The
derivative is taken within `[0, ∞)`, so it is one-sided at `t = 0` and the values of `V` at
negative times play no role. This is the covariance of the solution of `dU = DF(x(t)) U dt + dM`
when `M` is a Gaussian martingale with `d⟨M⟩ = G(x(t)) dt` and `U(0)` is centered Gaussian with
covariance `V₀`, independent of `M`: `hasGaussianLaw_isFluctuationPath`.
