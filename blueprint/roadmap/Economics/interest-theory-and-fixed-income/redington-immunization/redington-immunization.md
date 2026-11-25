# Local (Redington) immunization

Let the asset and liability values `A` and `L`, real functions of the rate, be differentiable
at every rate near `r₀`, with derivatives `A′` and `L′` differentiable at `r₀`, so their dollar
durations (`-A′`, `-L′`) and dollar convexities (`A″`, `L″`) are defined there. If the values
match, `A(r₀) = L(r₀)`, the dollar durations match, `A′(r₀) = L′(r₀)`, and the asset dollar
convexity strictly exceeds the liability dollar convexity, `A″(r₀) > L″(r₀)`, then the surplus
`A(r) - L(r)` is nonnegative for all rates `r` sufficiently close to `r₀`. This is local
protection against small parallel yield shifts only, not global protection and not protection
against curve twists. No positive matched value is assumed, so the conditions are stated on
the derivatives themselves, not on modified duration and convexity, which divide by the
matched value.
