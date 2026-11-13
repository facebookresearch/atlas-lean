# Pearson's chi-square theorem with estimated parameters

**Pearson's chi-square theorem with estimated parameters** (fixed cells, `k - 1 - s`
degrees of freedom). Let the cell probabilities follow a model `θ ↦ pθ θ` on a
finite-dimensional parameter space `F` (`pθ θ i ≥ 0` for every `θ`, `∑ᵢ pθ θ i = 1` for `θ`
near `θ₀`), with
true parameter `θ₀`, all `pθ θ₀ i > 0`, and Fréchet derivative `D` at `θ₀`. Write
`J a = ((D a)ᵢ / √(pθ θ₀ i))ᵢ` for the weighted Jacobian and `V = range J` for the weighted
tangent space.

The estimator hypothesis is the **efficient grouped-count estimator** condition: for some
continuous linear `L` with `J ∘ L` the orthogonal projection onto `V` (that is,
`L = (JᵀJ)⁻¹ Jᵀ` when `J` is injective),
`√n (θ̂ n - θ₀) = L (Pearson residuals at θ₀) + o_P(1)`. This is the asymptotic linear
expansion of the grouped-data maximum-likelihood and minimum chi-square estimators
(Cramér 1946, §30.3; Birch 1964); it is assumed here, not proved, and it is exactly what makes
the limit chi-square: other estimators (e.g. the ungrouped MLE) give a different limit in
general (Chernoff–Lehmann 1954).

Under these hypotheses Pearson's statistic with the fitted probabilities
`∑ᵢ (Nᵢ - n pᵢ(θ̂))² / (n pᵢ(θ̂))` converges in distribution to `χ²_{k - 1 - dim V}`. The proof
applies the delta method to `(r, θ) ↦ r - (w(pθ θ) - w(pθ θ₀))` jointly in the Pearson residuals
and `θ̂`, giving the limit `P_K Z - P_V (P_K Z) = P_{Vᗮ ⊓ K} Z` (the tangent space lies in
`K = (√p)ᗮ` because `∑ᵢ pθ θ i = 1`), and Cochran's theorem on the subspace `Vᗮ ⊓ K` of
dimension `k - 1 - dim V`. Fitted cells with `pᵢ(θ̂) = 0` contribute `0`; the event has
probability tending to `0`.

The nonnegativity hypothesis `hnn` is global although only `θ` near `θ₀` matter: since
`θ̂ n → θ₀` in probability, it could be localized to a neighbourhood of `θ₀` by comparing the
statistics on events of probability tending to `1`. That localization is not done here (a
follow-up); models that leave the simplex away from `θ₀`, such as Hardy–Weinberg proportions
`(θ², 2θ(1 - θ), (1 - θ)²)` on all of `ℝ`, must for now be reparametrized or clamped.
