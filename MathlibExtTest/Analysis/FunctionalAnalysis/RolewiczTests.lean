/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.Rolewicz
public import MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex

/-!
# Tests for Rolewicz's theorem

* `2 • B`, `-2 • B` are hypercyclic on `ℓ²(ℕ, ℂ)`; `(1 / 2) • B`, `1 • B`,
  and `I • B` are not.
* `3 • B` is hypercyclic on `ℓ²(ℕ, ℝ)`; `1 • B` is not.
* Pointwise actions of powers of the shifts, the `Bⁿ Fⁿ = 1` identity,
  and the norm of a power of the forward shift.
* `#print axioms` for the `2 • B` instance: standard triple only.
-/

open Set Filter Topology Metric
open scoped _root_.lp ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
open MathlibExt.Analysis.FunctionalAnalysis.Rolewicz
open MathlibExt.Analysis.InnerProductSpace

namespace MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests

/-- `2 • B` is hypercyclic on `ℓ²(ℕ, ℂ)`. -/
theorem rolewicz_two_complex : IsHypercyclic ((2 : ℂ) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) :=
  (isHypercyclic_smul_backwardShiftCLM_iff (2 : ℂ)).mpr (by
    rw [Complex.norm_two]
    norm_num)

/-- `-2 • B` is hypercyclic on `ℓ²(ℕ, ℂ)`. -/
example : IsHypercyclic (((-2 : ℂ)) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, norm_neg, Complex.norm_two]
  norm_num

/-- `(1 / 2) • B` is not hypercyclic on `ℓ²(ℕ, ℂ)`. -/
example : ¬ IsHypercyclic (((1 / 2 : ℂ)) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, Complex.norm_div, norm_one,
    Complex.norm_two]
  norm_num

/-- `1 • B` is not hypercyclic on `ℓ²(ℕ, ℂ)`. -/
example : ¬ IsHypercyclic (((1 : ℂ)) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, norm_one]
  norm_num

/-- `I • B` is not hypercyclic on `ℓ²(ℕ, ℂ)`: `‖I‖ = 1`. -/
example : ¬ IsHypercyclic (Complex.I • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, Complex.norm_I]
  norm_num

/-- `3 • B` is hypercyclic on `ℓ²(ℕ, ℝ)`. -/
example : IsHypercyclic ((3 : ℝ) • LpShiftOperator.backwardCLM (𝕜 := ℝ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff (𝕜 := ℝ)]
  norm_num

/-- `1 • B` is not hypercyclic on `ℓ²(ℕ, ℝ)`. -/
example : ¬ IsHypercyclic (((1 : ℝ)) • LpShiftOperator.backwardCLM (𝕜 := ℝ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff (𝕜 := ℝ), norm_one]
  norm_num

/-- The second power of the backward shift drops two coordinates. -/
example (x : ℓ²(ℕ, ℂ)) : (LpShiftOperator.backwardCLM (𝕜 := ℂ) ^ 2) x 3 = x 5 :=
  ShiftFredholmIndex.backwardCLM_pow_apply 2 x 3

/-- The second power of the forward shift vanishes in coordinate `0`. -/
example (x : ℓ²(ℕ, ℂ)) : (LpShiftOperator.shiftCLM (𝕜 := ℂ) ^ 2) x 0 = 0 := by
  rw [ShiftFredholmIndex.shiftCLM_pow_apply]
  simp

/-- `B F = 1` on the first basis vector. -/
example : (LpShiftOperator.backwardCLM (𝕜 := ℂ) ^ 1)
    ((LpShiftOperator.shiftCLM (𝕜 := ℂ) ^ 1) (lp.single 2 0 (1 : ℂ))) =
    lp.single 2 0 (1 : ℂ) := by
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
      DFunLike.congr_fun
        (ShiftFredholmIndex.backwardCLM_pow_comp_shiftCLM_pow (𝕜 := ℂ) 1)
        (lp.single 2 0 (1 : ℂ))

/-- Powers of the forward shift preserve norms. -/
example (x : ℓ²(ℕ, ℂ)) : ‖(LpShiftOperator.shiftCLM (𝕜 := ℂ) ^ 3) x‖ = ‖x‖ :=
  norm_forwardShiftCLM_pow_apply 3 x

/-- `ℚ + ℚ * I` is dense in `ℂ`; the approximant for `(1 / 2, 1 / 3)`
lies in its range. -/
example : ratApproxScalar (𝕜 := ℂ) (1 / 2, 1 / 3) ∈
    Set.range (ratApproxScalar (𝕜 := ℂ)) :=
  ⟨(1 / 2, 1 / 3), rfl⟩

#print axioms rolewicz_two_complex

/-- A nonreal scalar of norm two makes the canonical backward shift hypercyclic. -/
example : IsHypercyclic ((2 * Complex.I : ℂ) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, norm_mul,
    Complex.norm_two, Complex.norm_I, mul_one]
  norm_num

/-- Reversing the shift composition loses the first basis vector. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ) ∘L LpShiftOperator.backwardCLM)
    (lp.single 2 0 (1 : ℂ)) = 0 := by
  ext i
  cases i <;> simp [ContinuousLinearMap.comp_apply, LpShiftOperator.shiftCLM_apply,
    LpShiftOperator.backwardCLM_apply, lp.single_apply]

/-- Scalar powers and canonical backward powers have the correct coordinate action. -/
example (μ : ℂ) (n : ℕ) (x : ℓ²(ℕ, ℂ)) :
    (((μ • LpShiftOperator.backwardCLM (𝕜 := ℂ)) ^ n) x) 0 = μ ^ n * x n := by
  rw [smul_backwardShiftCLM_pow_apply, lp.coeFn_smul, Pi.smul_apply,
    ShiftFredholmIndex.backwardCLM_pow_apply, Nat.zero_add, smul_eq_mul]

end MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests
