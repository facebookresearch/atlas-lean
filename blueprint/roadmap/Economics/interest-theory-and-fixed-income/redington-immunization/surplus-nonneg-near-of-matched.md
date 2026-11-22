# Abstract surplus lemma

If the surplus is zero at `r₀`, its first
derivative vanishes at `r₀`, its second derivative is strictly positive at
`r₀`, and the surplus is continuous at `r₀`, then the surplus stays nonnegative
for all rates sufficiently close to `r₀`. The hypotheses constrain only the
difference `A - L`, not `A` and `L` themselves: they do not make the asset or
liability value differentiable, and Lean's `deriv` is `0` where a function is
not differentiable. So they do not by themselves certify the Redington
conditions; the faithful Redington statement, with the duration and convexity
conditions stated on `A` and `L`, is `redington_immunization`. This is the
nonnegative corollary of `surplus_pos_near_of_matched`.
