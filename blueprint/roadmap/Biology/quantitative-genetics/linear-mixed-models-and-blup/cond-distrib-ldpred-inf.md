# The LDpred-inf posterior

**The LDpred-inf posterior** (Vilhjálmsson et al. 2015; the likelihood
`β̂ | β ~ N(R β, R / N)` of Zhu and Stephens 2017): with `M` markers, `N` individuals,
heritability `h² > 0`, effects `β ~ N(0, h² / M · I)`, an LD matrix `R` that is positive definite,
and marginal estimates `β̂ = R β + ε` with `ε ~ N(0, R / N)` independent of `β`, the posterior law
of `β` given `β̂` is `N((R + M / (N h²) · I)⁻¹ β̂, (1 / N) (R + M / (N h²) · I)⁻¹)`. In particular
`𝔼[β | β̂] = (R + M / (N h²) · I)⁻¹ β̂`.
