# Sharpe–Lotka–Feller renewal theorem

**Sharpe–Lotka–Feller renewal theorem** (Feller 1941; Franco, Gyllenberg and Diekmann 2021,
Theorem 5.4). Let the net maternity function `φ` be measurable, nonnegative and zero on
`(-∞, 0)`, let `r` be a real root of the characteristic equation `∫ e^{-ra} φ(a) da = 1` (this
forces `a ↦ e^{-ra} φ(a)` to be integrable), and let the mean age at childbearing in the stable
population, `μ_r = ∫ a e^{-ra} φ(a) da`, be finite. Let the forcing `G` be measurable,
nonnegative and zero on `(-∞, 0)`, with `e^{-rt} G(t)` directly Riemann integrable. Let `B`
solve the renewal equation `B(t) = G(t) + ∫ B(t - a) φ(a) da` for every real `t`, where `B` is
measurable and zero on `(-∞, 0)` (so the integral runs over `[0, t]`) and `e^{-rt} B(t)` is
bounded on every half-line `(-∞, T]`. Then `e^{-rt} B(t) → (∫_0^∞ e^{-rs} G(s) ds) / μ_r` as
`t → ∞`.

## Sources

- Franco, Gyllenberg and Diekmann (2021), Definition 5.3, Theorem 5.4 and the proof of Theorem 3.13; Feller (1941).
