/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.Choquet

open MeasureTheory Set

-- The singleton case works without a second-countability hypothesis on the ambient space.
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] (x : X) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ ({x} : Set X)ᶜ = 0) (hbar : x = ∫ y, y ∂μ) :
    μ = Measure.dirac x :=
  MathlibExt.Analysis.ChoquetWanted.Analysis.bauer_unique
    (K := {x}) (hK_cpt := isCompact_singleton) (hK_cvx := convex_singleton x)
    (hx := by simp) (μ := μ) (hμ := hμ) (hbar := hbar)

-- An endpoint of a non-singleton compact convex set is also covered.
example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Icc 0 1)ᶜ = 0) (hbar : 0 = ∫ y, y ∂μ) : μ = Measure.dirac 0 := by
  refine MathlibExt.Analysis.ChoquetWanted.Analysis.bauer_unique
    (Icc 0 1) isCompact_Icc (convex_Icc 0 1) ?_ μ hμ hbar
  refine mem_extremePoints_iff_left.mpr ⟨by simp, ?_⟩
  intro y hy z hz hseg
  rcases hseg with ⟨a, b, ha, hb, _, hsum⟩
  rw [smul_eq_mul, smul_eq_mul] at hsum
  refine le_antisymm (le_of_not_gt fun hypos => ?_) hy.1
  exact (ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos ha hypos) (mul_nonneg hb.le hz.1))) hsum
