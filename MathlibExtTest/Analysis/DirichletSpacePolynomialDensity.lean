/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.DirichletSpacePolynomialDensity
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Tests for `MathlibExt.Analysis.DirichletSpacePolynomialDensity` -/

namespace MathlibExtTest.DirichletSpacePolynomialDensity

open MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted

-- Test section: the theorem, applied directly. Density of `Pg` passes to every `f` that dominates
-- `g` on the disc.
example (g f : DirichletSpace) (hg : IsDirichletDense (polyTimes g))
    (hgf : ∀ z : ℂ, ‖z‖ < 1 → ‖g.val z‖ ≤ ‖f.val z‖) : IsDirichletDense (polyTimes f) :=
  conjecture_holds g f hg hgf

-- Unfolding the conclusion: every `u` in the Dirichlet space is approximated, in the Dirichlet
-- norm, by an element agreeing on the disc with a polynomial multiple of `f`.
example (g f u : DirichletSpace) (hg : IsDirichletDense (polyTimes g))
    (hgf : ∀ z : ℂ, ‖z‖ < 1 → ‖g.val z‖ ≤ ‖f.val z‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∃ h : DirichletSpace,
      (∀ z : ℂ, ‖z‖ < 1 → h.val z = p.eval z * f.val z) ∧
      ‖h.val 0 - u.val 0‖ ^ 2 +
        ∫ z in Metric.ball (0 : ℂ) 1, ‖deriv h.val z - deriv u.val z‖ ^ 2 < ε := by
  obtain ⟨h, ⟨p, hp⟩, hlt⟩ := conjecture_holds g f hg hgf u ε hε
  exact ⟨p, h, hp, hlt⟩

/-- The multiple `c g` of an element `g` of the Dirichlet space, as an element of the space. -/
private noncomputable def smulElem (c : ℂ) (g : DirichletSpace) : DirichletSpace :=
  ⟨fun z => c * g.val z, analyticOn_const.mul g.property.1, by
    have heq : (fun z => ‖deriv (fun w => c * g.val w) z‖ ^ 2) =
        fun z => ‖c‖ ^ 2 * ‖deriv g.val z‖ ^ 2 := by
      funext z
      simp only [deriv_const_mul_field', norm_mul, mul_pow]
    rw [heq]
    exact g.property.2.const_mul _⟩

-- Test section: a consequence. If `Pg` is dense, so is `P(c g)` for every `c` with `1 ≤ ‖c‖`,
-- since `c g` dominates `g` on the disc.
example (g : DirichletSpace) (hg : IsDirichletDense (polyTimes g)) {c : ℂ} (hc : 1 ≤ ‖c‖) :
    IsDirichletDense (polyTimes (smulElem c g)) := by
  refine conjecture_holds g (smulElem c g) hg fun z _ => ?_
  change ‖g.val z‖ ≤ ‖c * g.val z‖
  rw [norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hc

/-- The constant function `a` as an element of the Dirichlet space. -/
private def constElem (a : ℂ) : DirichletSpace :=
  ⟨fun _ => a, analyticOn_const, by simp⟩

-- Test section: an edge case. Density of `Pg` is a real constraint on `g`: the polynomial
-- multiples of the zero function all vanish at `0`, so they stay at distance `1` from the
-- constant `1`, and the theorem says nothing for `g = 0`.
example : ¬ IsDirichletDense (polyTimes (constElem 0)) := by
  intro hdense
  obtain ⟨h, ⟨p, hp⟩, hlt⟩ := hdense (constElem 1) 1 one_pos
  have h0 : h.val 0 = 0 := by
    have := hp 0 (by simp)
    simpa [constElem] using this
  have hint : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1,
      ‖deriv h.val z - deriv (constElem 1).val z‖ ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have h1 : ‖h.val 0 - (constElem 1).val 0‖ ^ 2 = 1 := by
    simp [h0, constElem]
  linarith

end MathlibExtTest.DirichletSpacePolynomialDensity
