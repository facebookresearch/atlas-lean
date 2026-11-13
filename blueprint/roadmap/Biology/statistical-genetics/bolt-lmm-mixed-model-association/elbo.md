# Mean-field evidence lower bound

The mean-field evidence lower bound
`-(n/2) log (2π σ_e²) - 𝔼_q ‖y - X β‖² / (2 σ_e²) - ∑ⱼ KL(qⱼ ‖ π)`, meaningful for `σ_e² > 0`.
It is the ELBO for admissible factors (finite KL); for an inadmissible factor `toReal` would turn
an infinite divergence into `0`, so all results assume admissibility.
