# Nelson Aalen Process

The **Nelson–Aalen process** `Âₙ = ∑_{k < n} ΔN_{k+1} / Y_{k+1}`, i.e. `∫ dN / Y`.

**Vanishing-risk convention**: the integrand is the totalized inverse `Y⁻¹`, so a step with
nobody at risk (`Y_{k+1} = 0`) contributes `ΔN_{k+1} · 0⁻¹ = 0`, whatever `ΔN_{k+1}` is
(`nelsonAalenProcess_succ_of_atRisk_eq_zero`). This is the indicator convention `J / Y` with
`J = 1{Y ≠ 0}` of Andersen–Borgan–Gill–Keiding (`1{Y > 0}` there, the same for `Y ≥ 0`).
