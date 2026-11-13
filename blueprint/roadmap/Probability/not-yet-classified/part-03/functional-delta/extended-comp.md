# Extended continuous mapping theorem

**Extended continuous mapping theorem** (van der Vaart, Theorem 18.11(i)). Let `U n ⇒ V`
and let `g n, g₀ : X → Y` satisfy `g n xₙ → g₀ x` whenever `xₙ → x ∈ X₀` with `xₙ ∈ D n`
(stated with the filter `atTop ×ˢ 𝓝 x` restricted to `{(n, y) | y ∈ D n}`). If `U n ∈ D n` a.s.
and `V ∈ X₀` a.s., then `g n (U n) ⇒ g₀ V`.

No continuity of `g n` or `g₀` is assumed; the measurability of `g n ∘ U n` and `g₀ ∘ V` is.
`X` needs `HasOuterApproxClosed` (e.g. any pseudo-metric space) for the portmanteau direction
"weak convergence ⇒ limsup on closed sets"; `X₀` need not be measurable.
