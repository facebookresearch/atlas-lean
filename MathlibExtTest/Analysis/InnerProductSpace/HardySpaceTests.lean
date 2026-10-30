/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HardySpace

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the Hardy space `H²(𝔻)` and its Szegő kernel

* The Szegő kernel at `0` is the first standard basis vector.
* Evaluation at `0` reads off the constant Taylor coefficient.
* Evaluation of a monomial at `z = 1/2` is `c * (1/2)ⁿ`.
* At `z = 1/2`, the kernel has squared norm `4/3` and evaluation has
  norm `1 / √(3/4)`.
* The kernel inner product at `1/2` and `1/3` is `6/5`.
* The kernel inner product at `I/2` and `1/2` is `(1 - I/4)⁻¹`.
* Taylor coefficients are bounded by the `H²` norm.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.HardySpaceTests

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.HardySpace

/-- `0` is in the unit disc. -/
theorem zero_mem_disc : ‖(0 : ℂ)‖ < 1 := by simp

/-- `1/2` is in the unit disc. -/
theorem half_mem_disc : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_real]
  norm_num

/-- `1/3` is in the unit disc. -/
theorem third_mem_disc : ‖((1 / 3 : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_real]
  norm_num

/-- `I/2` is in the unit disc. -/
theorem I_div_two_mem_disc : ‖Complex.I / 2‖ < 1 := by
  rw [norm_div, Complex.norm_I]
  norm_num

/-- The Szegő kernel at `0` is the first standard basis vector. -/
example : szegoKernel (0 : ℂ) zero_mem_disc = lp.single 2 0 (1 : ℂ) :=
  szegoKernel_zero _

/-- Evaluation at `0` of the second basis vector is `0`. -/
example : hardyEval (0 : ℂ) zero_mem_disc (lp.single 2 1 (5 : ℂ)) = 0 := by
  rw [hardyEval_zero]
  simp

/-- Evaluation of the monomial `3 * z²` at `z = 1/2` is `3/4`. -/
example : hardyEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 2 (3 : ℂ)) = 3 / 4 := by
  rw [hardyEval_single]
  push_cast
  norm_num

/-- Evaluation at `z = 1/2` of the monomial `2 * z³` is `1/4`. -/
example : hardyEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 3 (2 : ℂ)) = 1 / 4 := by
  rw [hardyEval_single]
  push_cast
  norm_num

/-- At `z = 1/2`, the Szegő kernel has squared norm `4/3`. -/
example : ‖szegoKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ ^ 2 = 4 / 3 := by
  rw [norm_sq_szegoKernel]
  simp
  norm_num

/-- At `z = 1/2`, the Szegő kernel has norm `1 / √(3/4)`. -/
example : ‖szegoKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ = 1 / Real.sqrt (3 / 4) := by
  rw [norm_szegoKernel]
  congr 1
  simp
  norm_num

/-- At `z = 1/2`, point evaluation has norm `1 / √(3/4)`. -/
example : ‖hardyEvalCLM ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ = 1 / Real.sqrt (3 / 4) := by
  rw [norm_hardyEvalCLM]
  congr 1
  simp
  norm_num

/-- The kernel inner product at `1/2` and `1/3` is `6/5`. -/
example : ⟪szegoKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc,
    szegoKernel ((1 / 3 : ℝ) : ℂ) third_mem_disc⟫ = (6 / 5 : ℂ) := by
  have hconj : (starRingEnd ℂ) ((1 / 3 : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) :=
    RCLike.conj_ofReal _
  rw [inner_szegoKernel_szegoKernel, hconj]
  push_cast
  norm_num

/-- The kernel inner product at `I/2` and `1/2` is `(1 - I/4)⁻¹`. -/
example : ⟪szegoKernel (Complex.I / 2) I_div_two_mem_disc,
    szegoKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc⟫ = (1 - Complex.I / 4)⁻¹ := by
  have hconj : (starRingEnd ℂ) ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    RCLike.conj_ofReal _
  rw [inner_szegoKernel_szegoKernel, hconj]
  congr 1
  push_cast
  ring

/-- The reproducing property at `z = 1/2` for the constant function `3`. -/
example : ⟪szegoKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc,
    lp.single 2 0 (3 : ℂ)⟫ = 3 := by
  show hardyEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 0 (3 : ℂ)) = 3
  rw [hardyEval_single]
  simp

/-- Taylor coefficients are bounded by the `H²` norm: the `3`rd coefficient
of `2 * e₃` has norm `2`, which is the norm of the vector. -/
example : ‖(lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ)) 3‖
    ≤ ‖(lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ))‖ :=
  abs_coeff_le_norm _ _

/-- The Taylor series of the monomial `z` at `z = 1/2` is summable. -/
example : Summable (fun n => (lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ)) n
    * ((1 / 2 : ℝ) : ℂ) ^ n) :=
  summable_hardyEval_terms _ half_mem_disc _

/-- Point evaluation at `z = 1/2` of the constant function `3` is `3`. -/
example : hardyEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 0 (3 : ℂ)) = 3 := by
  rw [hardyEval_single]
  simp

end MathlibExtTest.Analysis.InnerProductSpace.HardySpaceTests
