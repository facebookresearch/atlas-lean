# The limit fluctuation is Gaussian with covariance `V(t)`

Let the driving data `(U₀, M)`
be jointly Gaussian as one random element `Z` of `ℝ² × C([0, T], ℝ²)` (`hZ`, `hZU₀`, `hZM`),
centered, with `U₀` of covariance `V₀` and uncorrelated with the increments of `M`, and with
`E[(M(s) - M(0)) (M(r) - M(0))ᵀ] = K(min s r)` for `K(t) = ∫₀ᵗ G(x)` (`quadCov`): the
covariance of the Gaussian martingale with `d⟨M⟩ = G(x(t)) dt` of the diffusion approximation.
Then the solution `U` of the fluctuation equation has, at each `t ∈ [0, T]`, a Gaussian law with
mean `0` and second moments `E[⟨a, U(t)⟩ ⟨b, U(t)⟩] = ⟨a, V(t) b⟩`, where `V` is the limit
covariance (`IsLimitCovariance`); `covariance_isFluctuationPath` restates the last part entrywise.

The proof writes `⟨ℓ, U(t)⟩` as the integration-by-parts Wiener integral
`⟨y(0), U₀⟩ + ∫₀ᵗ ⟨y(s), dM(s)⟩` against the adjoint solution `y' = -DF(x)ᵀ y`, `y(t) = ℓ`
(`IsFluctuationPath.dot_eq`), a continuous linear functional of `Z`. Gaussianity follows; the
Wiener isometry `E[(∫ y_a dM) (∫ y_b dM)] = ∫₀ᵗ ⟨y_b, G y_a⟩` follows from the covariance of `M`
(`wienerIsometry_aux`); and the Lyapunov equation transports `⟨y_a, V y_b⟩` along the same flow
(`IsLimitCovariance.quadForm_eq`).
