# Sharpe–Lotka–Feller renewal theorem

**Sharpe–Lotka–Feller renewal theorem** (Feller 1941; Feller 1971, §XI.1). Let the net
maternity function `φ` be measurable, nonnegative and zero on `(-∞, 0)`, let `r` be a real root
of the characteristic equation `∫ e^{-ra} φ(a) da = 1` (this forces `a ↦ e^{-ra} φ(a)` to be
integrable), and let the mean age at childbearing in the stable population,
`μ_r = ∫ a e^{-ra} φ(a) da`, be finite. Let `B` solve the renewal equation
`B(t) = G(t) + ∫ B(t - a) φ(a) da` for every real `t`, where the tilted pair
`(e^{-rt} B(t), e^{-rt} G(t))` is `KeyRenewalAdmissible` (so `B` and `G` vanish on `(-∞, 0)`,
the integral runs over `[0, t]`, `B` is bounded on compact sets, and `e^{-rt} G(t)` satisfies
Feller's sufficient condition for direct Riemann integrability). Then
`e^{-rt} B(t) → (∫_0^∞ e^{-rs} G(s) ds) / μ_r` as `t → ∞`.

## Sources

- Feller (1941); Feller (1971), §XI.1; Franco, Gyllenberg and Diekmann (2021), Theorem 5.4.
