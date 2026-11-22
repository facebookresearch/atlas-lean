# Local (Redington) immunization

Let the asset and liability values `A`
and `L` be differentiable near `r₀`, with derivatives differentiable at `r₀`, so
their dollar durations (the negated first derivatives) and dollar convexities
(the second derivatives) are defined there. If the values match at `r₀`
(`A r₀ = L r₀`), the dollar durations match (`deriv A r₀ = deriv L r₀`), and the
asset dollar convexity strictly exceeds the liability dollar convexity
(`deriv (deriv L) r₀ < deriv (deriv A) r₀`), then the surplus stays nonnegative
for all rates sufficiently close to `r₀`. This is local protection against
small parallel yield shifts only, not global protection and not protection
against curve twists. No positive matched present value is assumed, so the
hypotheses are not identified here with modified duration / convexity, which
divide by the matched value. The strict conclusion at `r ≠ r₀` is
`redington_immunization_strict`.
