/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Epidemiology.NextGenerationOperator
import Mathlib.Tactic.NormNum

/-!
# Tests for generation growth with a separable kernel

Compute the integral and the radius separately on a one-point space, including a positive value
and the zero-measure case. Also check that the positive example satisfies the theorem's hypotheses.
-/

open MeasureTheory
open WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted

private abbrev Point := PUnit.{1}

local notation "μ₁" => Measure.dirac (PUnit.unit : Point)
local notation "E" => Lp ℝ 1 μ₁
local notation "K₁" => (3 : ℝ) • (1 : E →L[ℝ] E)

private theorem onePoint_nontrivial : Nontrivial E := by
  let h : MemLp (fun _ : Point => (1 : ℝ)) 1 μ₁ := memLp_const 1
  refine ⟨⟨h.toLp _, 0, ?_⟩⟩
  intro heq
  have he : (fun _ : Point => (1 : ℝ)) =ᵐ[μ₁] 0 :=
    h.coeFn_toLp.symm.trans (heq ▸ Lp.coeFn_zero ℝ 1 μ₁)
  simp [ae_dirac_eq, Filter.EventuallyEq, Filter.eventually_pure] at he

-- Independent computation of the integral for `a = 3`, `b = 1/2`, `S = 2`.
example : (∫ _ : Point, (1 / 2 : ℝ) * 2 * 3 ∂μ₁) = 3 := by
  rw [integral_dirac]
  norm_num

-- Compute the radius of `3 • 1` without the separable-kernel theorem.
example : gelfandRadius (K₁) = 3 := by
  let : Nontrivial E := onePoint_nontrivial
  rw [gelfandRadius_smul, gelfandRadius_one]
  norm_num

-- With zero measure both sides vanish, including on the subsingleton `L¹` space.
local notation "E₀" => Lp ℝ 1 (0 : Measure Point)

example : gelfandRadius (0 : E₀ →L[ℝ] E₀) =
    ∫ _ : Point, (1 / 2 : ℝ) * 2 * 3 ∂(0 : Measure Point) := by
  simp

-- Client example: verify the separable action for every input, then apply the public theorem.
example : generationGrowth (K₁) = ∫ _ : Point, (1 / 2 : ℝ) * 2 * 3 ∂μ₁ := by
  refine generationGrowth_eq_integral_of_separable (μ := μ₁)
    (fun _ => 3) (fun _ => 1 / 2) (fun _ => 2)
    measurable_const measurable_const measurable_const (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (memLp_const _) (integrable_const _) (K₁) ?_
  intro φ
  have h := Lp.coeFn_smul (3 : ℝ) φ
  rw [ae_dirac_eq] at h ⊢
  simp only [Filter.EventuallyEq, Filter.eventually_pure, smul_apply,
    one_apply_eq_self, Pi.smul_apply, smul_eq_mul, integral_dirac] at h ⊢
  rw [h, ← mul_assoc]
  norm_num
