/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.LpDimensionBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.MeasureTheory.Function.LpDimensionBound

/-- Consumer with the original binders. -/
theorem exactSource {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal :=
  MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm V C hV

/-- The zero subspace satisfies the bound with `C = 0`. -/
example {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {𝕜 : Type*} [RCLike 𝕜] :
    FiniteDimensional 𝕜 (⊥ : Submodule 𝕜 (Lp 𝕜 2 μ)) ∧
      (Module.finrank 𝕜 (⊥ : Submodule 𝕜 (Lp 𝕜 2 μ)) : ℝ) ≤
        0 ^ 2 * (μ Set.univ).toReal := by
  refine exactSource ⊥ 0 ?_
  intro φ hφ
  rw [Submodule.mem_bot] at hφ
  subst hφ
  filter_upwards [MeasureTheory.Lp.coeFn_zero 𝕜 2 μ] with x hx
  simp only [hx, Pi.zero_apply, norm_zero, zero_mul, le_refl]

end MathlibExtTest.MeasureTheory.Function.LpDimensionBound
