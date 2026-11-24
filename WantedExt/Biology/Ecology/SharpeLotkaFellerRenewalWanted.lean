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
non-lattice. Direct Riemann integrability is represented by the library's
`KeyRenewalAdmissible` pair: the tilted forcing is measurable, vanishes on `(-∞, 0)`, is
continuous almost everywhere and is dominated on `[0, ∞)` by an antitone integrable function
(Feller's sufficient condition for direct Riemann integrability), and the tilted solution
vanishes on `(-∞, 0)` and is bounded on every half-line `(-∞, T]`. The forcing may take either
sign; the biological case `G ≥ 0` is a special case.

Sources: W. Feller, "On the integral equation of renewal theory", Ann. Math. Statist. 12
(1941) 243–267; W. Feller, *An Introduction to Probability Theory and Its Applications*,
vol. II, 2nd ed. (1971), §XI.1 (renewal theorem, direct Riemann integrability); E. Franco,
M. Gyllenberg and O. Diekmann, "One dimensional reduction of a renewal equation for a
measure-valued function of time describing population dynamics", Acta Appl. Math. 175 (2021)
12, Definition 5.3 and Theorem 5.4.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Renewal.LatticeConstants

@[expose] public section

namespace WantedExt.Biology.Ecology.SharpeLotkaFellerRenewalWanted

open MeasureTheory Filter Topology Set Real MathlibExt.Probability.Renewal.LatticeConstants

/-- **Sharpe–Lotka–Feller renewal theorem** (Feller 1941; Feller 1971, §XI.1). Let the net
maternity function `φ` be measurable, nonnegative and zero on `(-∞, 0)`, let `r` be a real root
of the characteristic equation `∫ e^{-ra} φ(a) da = 1` (this forces `a ↦ e^{-ra} φ(a)` to be
integrable), and let the mean age at childbearing in the stable population,
`μ_r = ∫ a e^{-ra} φ(a) da`, be finite. Let `B` solve the renewal equation
`B(t) = G(t) + ∫ B(t - a) φ(a) da` for every real `t`, where the tilted pair
`(e^{-rt} B(t), e^{-rt} G(t))` is `KeyRenewalAdmissible` (so `B` and `G` vanish on `(-∞, 0)`,
the integral runs over `[0, t]`, `B` is bounded on compact sets, and `e^{-rt} G(t)` satisfies
Feller's sufficient condition for direct Riemann integrability). Then
`e^{-rt} B(t) → (∫_0^∞ e^{-rs} G(s) ds) / μ_r` as `t → ∞`.

Sources: Feller (1941); Feller (1971), §XI.1; Franco, Gyllenberg and Diekmann (2021),
Theorem 5.4. -/
public theorem_wanted tendsto_exp_neg_mul_births (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ a, 0 ≤ φ a) (hφneg : ∀ a < 0, φ a = 0) (r : ℝ)
    (hr : ∫ a, exp (-(r * a)) * φ a = 1)
    (hmean : Integrable (fun a => a * (exp (-(r * a)) * φ a)))
    (B G : ℝ → ℝ) (hren : ∀ t, B t = G t + ∫ a, B (t - a) * φ a)
    (hadm : KeyRenewalAdmissible (fun t => exp (-(r * t)) * B t)
      (fun t => exp (-(r * t)) * G t)) :
    Tendsto (fun t => exp (-(r * t)) * B t) atTop
      (𝓝 ((∫ s in Ioi 0, exp (-(r * s)) * G s) / ∫ a, a * (exp (-(r * a)) * φ a)))

end WantedExt.Biology.Ecology.SharpeLotkaFellerRenewalWanted
