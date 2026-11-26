# Crooks fluctuation theorem

Assume the setting `MicroReversible` (`bar` an involution;
positive initial probability vectors `ρ_F`, `ρ_R`; stochastic matrices `M`, `MR`; forward and
reverse heats with `QR[x̄(-t)] = -QF[x]`; microscopic reversibility with `QF`). Then for every
real `ω`, the probabilities `P_F(ω) = ∑_{x : ω_F[x] = ω} P_F[x]` and
`P_R(-ω) = ∑_{y : ω_R[y] = -ω} P_R[y]` satisfy `P_F(+ω) = e^{ω} P_R(-ω)` (Crooks 1999, Eq. (2)),
where `ω_F[x] = ln ρ_F(x_0) - ln ρ_R(x̄_n) - β QF[x]` and
`ω_R[y] = ln ρ_R(y_0) - ln ρ_F(ȳ_n) - β QR[y]` are the path functionals of the forward and
reverse processes (`entropyProduction`), for arbitrary positive initial laws `ρ_F`, `ρ_R`. Each
agrees with the log-ratio of the probabilities of a path and of its time reversal on their common
positive support, and extends it to the paths where both probabilities vanish. They are Crooks's
entropy productions when `ρ_R` is the time reversal of the final density of the forward process
(and `ρ_F` that of the reverse process), as in the source.

## Sources

- G. E. Crooks, "Entropy production fluctuation theorem and the nonequilibrium work relation for free energy differences", Phys. Rev. E 60 (1999) 2721–2726, Eq. (2) (arXiv:cond-mat/9901352).
