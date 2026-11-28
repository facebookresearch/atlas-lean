# Nonequilibrium work relation

Assume the setting `MicroReversible` with `β > 0` and
canonical initial densities: `ρ_F(s) = e^{-β E_0(s)} / Z_0` and
`ρ_R(bar s) = e^{-β E_1(s)} / Z_1` for all `s`, with `Z_0 = ∑_s e^{-β E_0(s)}` and
`Z_1 = ∑_s e^{-β E_1(s)}`. Let the work be `W[x] = E_1(x_n) - E_0(x_0) - QF[x]` and
`ΔF = -β⁻¹ ln Z_1 + β⁻¹ ln Z_0`. Then the forward path functional
`ω_F[x] = ln ρ_F(x_0) - ln ρ_R(x̄_n) - β QF[x]` (`entropyProduction` with the forward heat `QF`,
which agrees with the forward path log-ratio where that is defined) is `β (W[x] - ΔF)` for every
path (Crooks 1999, Eq. (10)), and `∑_x P_F[x] e^{-β W[x]} = e^{-β ΔF}` (Eq. (3)). Canonical
initial densities do not make the final density of the forward process that of `E_1` (identity
transitions keep `ρ_F`), so `ω_F` is the entropy production of Eq. (6) only when the forward
process ends in the equilibrium of `E_1`, as in the source, where the system relaxes to it after
the driving; the work relation holds without this.

## Sources

- G. E. Crooks, "Entropy production fluctuation theorem and the nonequilibrium work relation for free energy differences", Phys. Rev. E 60 (1999) 2721–2726, Eqs. (10) and (3) (arXiv:cond-mat/9901352).
