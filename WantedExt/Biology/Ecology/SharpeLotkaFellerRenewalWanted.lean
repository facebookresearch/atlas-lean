/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Sharpe–Lotka–Feller renewal theorem: births grow like `Q e^{rt}`

In stable population theory the birth rate `B` satisfies the renewal (Lotka) equation
`B(t) = G(t) + ∫_0^t B(t - a) φ(a) da`, where `φ ≥ 0` is the net maternity function (survival
times fecundity) and `G` collects births to the initial population. If `r` is the real root of
`∫ e^{-ra} φ(a) da = 1` and `μ_r = ∫ a e^{-ra} φ(a) da` is finite, then
`e^{-rt} B(t) → Q = (∫_0^∞ e^{-rt} G(t) dt) / μ_r`.

The reduction to the case `∫ φ = 1` by the tilt `φ_r(a) = e^{-ra} φ(a)`,
`B_r(t) = e^{-rt} B(t)`, `G_r(t) = e^{-rt} G(t)` is proved in
`MathlibExt.Probability.Renewal.LatticeConstants` (`tendsto_scaled_of_keyRenewal`), but only
under the key renewal theorem for the tilted law as a hypothesis. The missing statement recorded
here is the renewal theorem for a law with a density, so the tilted law is automatically
non-lattice. As in Franco, Gyllenberg and Diekmann (2021), Theorem 5.4, the forcing is
nonnegative, as births to the initial population are, and its tilt `e^{-rt} G(t)` is directly
Riemann integrable in the sense of their Definition 5.3 (`DirectlyRiemannIntegrable`); the
solution `B` is measurable, vanishes on `(-∞, 0)`, and its tilt is bounded on every half-line
`(-∞, T]`, which singles it out among the solutions of the equation.

Sources: W. Feller, "On the integral equation of renewal theory", Ann. Math. Statist. 12
(1941) 243–267; W. Feller, *An Introduction to Probability Theory and Its Applications*,
vol. II, 2nd ed. (1971), §XI.1 (renewal theorem, direct Riemann integrability); E. Franco,
M. Gyllenberg and O. Diekmann, "One dimensional reduction of a renewal equation for a
measure-valued function of time describing population dynamics", Acta Appl. Math. 175 (2021)
12, Definition 5.3, Theorem 5.4 and the proof of Theorem 3.13.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Renewal.LatticeConstants

@[expose] public section

namespace WantedExt.Biology.Ecology.SharpeLotkaFellerRenewalWanted

open MeasureTheory Filter Topology Set Real MathlibExt.Probability.Renewal.LatticeConstants

/-- **Direct Riemann integrability** (Franco, Gyllenberg and Diekmann 2021, Definition 5.3). A
function `f`, nonnegative on `[0, ∞)`, is directly Riemann integrable when, for the partition
`0 < h < 2h < ⋯` of `[0, ∞)`, the upper and lower Riemann sums
`∑_n h · sup_{[nh, (n+1)h]} f` and `∑_n h · inf_{[nh, (n+1)h]} f` are finite for every `h > 0`
and tend to the same finite limit as `h → 0`. The sums are taken in `[0, ∞]`, so a sum is
finite only when `f` is bounded on every cell and the series converges.

Source: Franco, Gyllenberg and Diekmann (2021), Definition 5.3. -/
def DirectlyRiemannIntegrable (f : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → 0 ≤ f t) ∧
    (∀ h : ℝ, 0 < h →
      ∑' n : ℕ, ENNReal.ofReal h * ⨆ t ∈ Icc (n * h) ((n + 1) * h), ENNReal.ofReal (f t) ≠ ⊤) ∧
    ∃ I : ENNReal, I ≠ ⊤ ∧
      Tendsto (fun h : ℝ => ∑' n : ℕ,
        ENNReal.ofReal h * ⨆ t ∈ Icc (n * h) ((n + 1) * h), ENNReal.ofReal (f t))
        (𝓝[>] 0) (𝓝 I) ∧
      Tendsto (fun h : ℝ => ∑' n : ℕ,
        ENNReal.ofReal h * ⨅ t ∈ Icc (n * h) ((n + 1) * h), ENNReal.ofReal (f t))
        (𝓝[>] 0) (𝓝 I)

/-- **Sharpe–Lotka–Feller renewal theorem** (Feller 1941; Franco, Gyllenberg and Diekmann 2021,
Theorem 5.4). Let the net maternity function `φ` be measurable, nonnegative and zero on
`(-∞, 0)`, let `r` be a real root of the characteristic equation `∫ e^{-ra} φ(a) da = 1` (this
forces `a ↦ e^{-ra} φ(a)` to be integrable), and let the mean age at childbearing in the stable
population, `μ_r = ∫ a e^{-ra} φ(a) da`, be finite. Let the forcing `G` be measurable,
nonnegative and zero on `(-∞, 0)`, with `e^{-rt} G(t)` directly Riemann integrable. Let `B`
solve the renewal equation `B(t) = G(t) + ∫ B(t - a) φ(a) da` for every real `t`, where `B` is
measurable and zero on `(-∞, 0)` (so the integral runs over `[0, t]`) and `e^{-rt} B(t)` is
bounded on every half-line `(-∞, T]`. Then `e^{-rt} B(t) → (∫_0^∞ e^{-rs} G(s) ds) / μ_r` as
`t → ∞`.

Sources: Franco, Gyllenberg and Diekmann (2021), Definition 5.3, Theorem 5.4 and the proof of
Theorem 3.13; Feller (1941). -/
public theorem_wanted tendsto_exp_neg_mul_births (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ a, 0 ≤ φ a) (hφneg : ∀ a < 0, φ a = 0) (r : ℝ)
    (hr : ∫ a, exp (-(r * a)) * φ a = 1)
    (hmean : Integrable (fun a => a * (exp (-(r * a)) * φ a)))
    (B G : ℝ → ℝ) (hren : ∀ t, B t = G t + ∫ a, B (t - a) * φ a)
    (hGm : Measurable G) (hG0 : ∀ t, 0 ≤ G t) (hGneg : ∀ t < 0, G t = 0)
    (hGdri : DirectlyRiemannIntegrable (fun t => exp (-(r * t)) * G t))
    (hBm : Measurable B) (hBneg : ∀ t < 0, B t = 0)
    (hBbdd : ∀ T, ∃ M, ∀ t ≤ T, |exp (-(r * t)) * B t| ≤ M) :
    Tendsto (fun t => exp (-(r * t)) * B t) atTop
      (𝓝 ((∫ s in Ioi 0, exp (-(r * s)) * G s) / ∫ a, a * (exp (-(r * a)) * φ a)))

end WantedExt.Biology.Ecology.SharpeLotkaFellerRenewalWanted
