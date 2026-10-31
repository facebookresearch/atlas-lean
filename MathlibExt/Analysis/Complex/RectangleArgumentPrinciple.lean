/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectangleResidue
public import Mathlib.Analysis.Analytic.Order

/-!
# The argument principle on a rectangle

For an entire function `E` of finite order at every point (i.e. not identically zero) and a
rectangle whose boundary avoids the zeros of `E`, the boundary integral of the logarithmic
derivative `E'/E` is `2πi` times the number of zeros inside, counted with multiplicity. This is
the residue theorem `RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum` applied to
`E'/E`, whose poles are simple with residue the order of the zero.

## Main statements

* `AnalyticAt.continuousAt_logDeriv`: `E'/E` is continuous where `E` is analytic and nonzero.
* `RectilinearRectangle.boundaryIntegral_logDeriv_eq`: the argument principle on a rectangle.
-/

open Complex Filter Topology

@[expose] public section

/-- The logarithmic derivative is continuous at a point where `E` is analytic and nonzero. -/
theorem AnalyticAt.continuousAt_logDeriv {E : ℂ → ℂ} {s : ℂ} (hE : AnalyticAt ℂ E s)
    (hs : E s ≠ 0) : ContinuousAt (logDeriv E) s := by
  have : logDeriv E = fun u => deriv E u / E u := by funext u; exact logDeriv_apply E u
  rw [this]
  exact hE.deriv.continuousAt.div hE.continuousAt hs

namespace RectilinearRectangle

/-- **The argument principle on a rectangle, for an entire function.** If `E` is entire with
finite order of vanishing everywhere, `Z` lies in the open rectangle and contains every zero of
`E` in the closed rectangle, then the boundary integral of `E'/E` is
`2πi ∑_{p ∈ Z} ord_p E`. -/
theorem boundaryIntegral_logDeriv_eq (r : RectilinearRectangle) {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) (Z : Finset ℂ)
    (hin : ∀ p ∈ Z, r.first.re < p.re ∧ p.re < r.second.re ∧ r.first.im < p.im ∧
      p.im < r.second.im)
    (hZ : ∀ s ∈ r.carrier, E s = 0 → s ∈ Z)
    (hfin : ∀ p, analyticOrderAt E p ≠ ⊤) :
    r.boundaryIntegral (logDeriv E) =
      2 * (Real.pi : ℂ) * I * ∑ p ∈ Z, ((analyticOrderAt E p).toNat : ℂ) := by
  set res : ℂ → ℂ := fun p => ((analyticOrderAt E p).toNat : ℂ) with hres
  have hloc : ∀ p ∈ Z, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, logDeriv E s = res p / (s - p) + φ s := by
    intro p _
    have hm : analyticOrderAt E p = ((analyticOrderAt E p).toNat : ℕ) :=
      (ENat.natCast_toNat (hfin p)).symm
    obtain ⟨E₁, hE₁a, hE₁0, hE₁e⟩ := (hE.analyticAt p).analyticOrderAt_eq_natCast.mp hm
    have hf : ∀ᶠ s in 𝓝[≠] p,
        E s = (s - p) ^ (((analyticOrderAt E p).toNat : ℕ) : ℤ) * E₁ s := by
      filter_upwards [nhdsWithin_le_nhds hE₁e] with s hs
      rw [hs, zpow_natCast, smul_eq_mul]
    have hL := eventually_logDeriv_eq_of_eq_zpow_mul hE₁a hE₁0 hf
    refine ⟨logDeriv E₁,
      (hE₁a.deriv.differentiableAt.div hE₁a.differentiableAt hE₁0).congr_of_eventuallyEq
        (Eventually.of_forall fun u => logDeriv_apply E₁ u), ?_⟩
    filter_upwards [hL] with s hs
    rw [hs]
    simp [hres]
  have hdiff : ∀ s ∈ r.carrier, s ∉ Z → DifferentiableWithinAt ℂ (logDeriv E) r.carrier s := by
    intro s hs hsZ
    have hE0 : E s ≠ 0 := fun h => hsZ (hZ s hs h)
    have : logDeriv E = fun u => deriv E u / E u := by funext u; exact logDeriv_apply E u
    rw [this]
    exact (((hE.analyticAt s).deriv.differentiableAt).div (hE s) hE0).differentiableWithinAt
  obtain ⟨g, hg, hfg⟩ :=
    exists_differentiableOn_eq_add_sum_div_sub _ Z res (logDeriv E) hloc hdiff
  exact boundaryIntegral_eq_two_pi_mul_I_mul_sum r Z res (logDeriv E) g hin hg hfg

end RectilinearRectangle
