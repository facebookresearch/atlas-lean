# Fk q2 subcritical decay of cov

Exponential decay `θ_n(β - 2δ) ≤ M e^{-n δ / Q}` (Duminil-Copin–Raoufi–Tassion, 2019),
conditional form.

The content is in the hypotheses: `hderiv` (derivative formula), `hcov` (OSSS inequality with
revealment), `hcRf` (positive lower bound on the prefactors), `hident` (normalization relating `Σ_n`
and `Sgn`), `hθmono` (monotonicity in `β`) and `hSpoly` (`Σ_n(β) ≤ n^{1-α}`, the subcritical case).
The differential inequality is derived from these, and the integration is proved. `_hJ` and `_hxpos`
are not used.

Fidelity: the integration lemma uses the rate `n / Σ_n` with constant `1`. `hident` forces
`Sgn = Σ_n c_R (1 - θ_n) / 4`, so `hcov` then asks for `∑_e Cov_e ≥ n θ_n / (c_R Σ_n)`. That is
stronger than the OSSS-revealment bound `∑_e Cov_e ≥ (n / (4 Σ_n)) θ_n (1 - θ_n)` by the factor
`4 / (c_R (1 - θ_n))`. In the literature this constant is carried in the rate `c n / Σ_n`
(equivalently, `β` is rescaled).
