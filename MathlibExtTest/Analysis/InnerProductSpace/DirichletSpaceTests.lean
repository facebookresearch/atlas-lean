/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.DirichletSpace

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the Dirichlet space `𝒟(𝔻)` and its reproducing kernel

* The Dirichlet kernel at `0` is the first standard basis vector.
* Evaluation at `0` reads off the constant Taylor coefficient.
* Evaluation of a monomial at `z = 1/2` is `c * zⁿ / √(n + 1)`.
* At `z = 1/2`, the kernel has squared norm `4 * log (4/3)` and
  evaluation has norm `√(4 * log (4/3))`.
* The kernel inner product at `1/2` and `1/3` is `6 * log (6/5)`.
* The kernel inner product at `0` and `1/2` is `1`.
* The Dirichlet kernel norm is bounded by the Hardy kernel norm at `1/2`.
* The Taylor series of a `𝒟` function converges absolutely at `1/2`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.DirichletSpaceTests

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.DirichletSpace

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

/-- The norm of `1/2` in `ℂ`. -/
theorem norm_half : ‖((1 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
  rw [Complex.norm_real]
  norm_num

/-- The log identity for the kernel norm at `1/2`. -/
theorem log_identity_half :
    -Real.log (1 - (1 / 2 : ℝ) ^ 2) / (1 / 2 : ℝ) ^ 2 = 4 * Real.log (4 / 3) := by
  have hlog : Real.log (4 / 3 : ℝ) = -Real.log (3 / 4 : ℝ) := by
    rw [show (4 / 3 : ℝ) = (3 / 4)⁻¹ by norm_num, Real.log_inv]
  rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num,
    show ((1 / 2 : ℝ)) ^ 2 = 1 / 4 by norm_num, ← hlog,
    div_eq_iff (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  ring

/-- The Dirichlet kernel at `0` is the first standard basis vector. -/
example : dirichletKernel (0 : ℂ) zero_mem_disc = lp.single 2 0 (1 : ℂ) :=
  dirichletKernel_zero _

/-- Evaluation at `0` of the second basis vector is `0`. -/
example : dirichletEval (0 : ℂ) zero_mem_disc (lp.single 2 1 (5 : ℂ)) = 0 := by
  rw [dirichletEval_zero]
  simp

/-- Evaluation of the constant function `3` at `1/2` is `3`. -/
example : dirichletEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 0 (3 : ℂ)) = 3 := by
  rw [dirichletEval_single]
  simp

/-- Evaluation of the monomial `5 * z³ / 2` at `1/2` is `5 / 16`. -/
example : dirichletEval ((1 / 2 : ℝ) : ℂ) half_mem_disc (lp.single 2 3 (5 : ℂ)) =
    5 / 16 := by
  rw [dirichletEval_single]
  have hcast : (Real.sqrt (((3 : ℕ) : ℝ) + 1) : ℂ) = 2 := by
    have h2 : Real.sqrt (((3 : ℕ) : ℝ) + 1) = 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
      norm_num
    rw [h2]
    norm_num
  rw [hcast]
  push_cast
  ring

/-- At `z = 1/2`, the Dirichlet kernel has squared norm `4 * log (4/3)`. -/
example : ‖dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ ^ 2 =
    4 * Real.log (4 / 3) := by
  rw [norm_sq_dirichletKernel_of_ne_zero _ half_mem_disc (by simp), norm_half,
    log_identity_half]

/-- At `z = 1/2`, the Dirichlet kernel has norm `√(4 * log (4/3))`. -/
example : ‖dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ =
    Real.sqrt (4 * Real.log (4 / 3)) := by
  rw [norm_dirichletKernel_of_ne_zero _ half_mem_disc (by simp), norm_half,
    log_identity_half]

/-- At `z = 1/2`, point evaluation has norm `√(4 * log (4/3))`. -/
example : ‖dirichletEvalCLM ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ =
    Real.sqrt (4 * Real.log (4 / 3)) := by
  rw [norm_dirichletEvalCLM_of_ne_zero _ half_mem_disc (by simp), norm_half,
    log_identity_half]

/-- At `z = 0`, the Dirichlet kernel has norm `1`. -/
example : ‖dirichletKernel (0 : ℂ) zero_mem_disc‖ = 1 :=
  norm_dirichletKernel_zero _

/-- At `z = 0`, point evaluation has norm `1`. -/
example : ‖dirichletEvalCLM (0 : ℂ) zero_mem_disc‖ = 1 :=
  norm_dirichletEvalCLM_zero _

/-- The kernel inner product at `1/2` and `1/3` is `6 * log (6/5)`. -/
example : ⟪dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc,
    dirichletKernel ((1 / 3 : ℝ) : ℂ) third_mem_disc⟫ =
    ((6 * Real.log (6 / 5) : ℝ) : ℂ) := by
  have h0 : ((1 / 2 : ℝ) : ℂ) * (starRingEnd ℂ) ((1 / 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.conj_ofReal]
    norm_num
  rw [inner_dirichletKernel_dirichletKernel_eq_log _ half_mem_disc _ third_mem_disc h0]
  have hu : ((1 / 2 : ℝ) : ℂ) * (starRingEnd ℂ) ((1 / 3 : ℝ) : ℂ) =
      ((1 / 6 : ℝ) : ℂ) := by
    rw [Complex.conj_ofReal]
    push_cast
    norm_num
  rw [hu]
  have h1 : (1 : ℂ) - ((1 / 6 : ℝ) : ℂ) = ((5 / 6 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [h1]
  have hlog : Complex.log ((5 / 6 : ℝ) : ℂ) = ((Real.log (5 / 6) : ℝ) : ℂ) :=
    (Complex.ofReal_log (show (0 : ℝ) ≤ 5 / 6 by norm_num)).symm
  rw [hlog]
  have hreal : -Real.log (5 / 6 : ℝ) / (1 / 6 : ℝ) = 6 * Real.log (6 / 5 : ℝ) := by
    have hlog2 : Real.log (6 / 5 : ℝ) = -Real.log (5 / 6 : ℝ) := by
      rw [show (6 / 5 : ℝ) = (5 / 6)⁻¹ by norm_num, Real.log_inv]
    rw [← hlog2, div_eq_iff (by norm_num : (1 / 6 : ℝ) ≠ 0)]
    ring
  exact_mod_cast hreal

/-- The kernel inner product at `0` and `1/2` is `1`. -/
example : ⟪dirichletKernel (0 : ℂ) zero_mem_disc,
    dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc⟫ = 1 := by
  rw [dirichletKernel_zero zero_mem_disc, lp.inner_single_left, RCLike.inner_apply']
  simp [dirichletKernel_apply]

/-- Evaluation of the kernel at its own point `1/2` is `4 * log (4/3)`. -/
example : dirichletEval ((1 / 2 : ℝ) : ℂ) half_mem_disc
    (dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc) =
    ((4 * Real.log (4 / 3) : ℝ) : ℂ) := by
  rw [dirichletEval_dirichletKernel_of_ne_zero _ half_mem_disc (by simp)]
  congr 1
  rw [norm_half]
  exact log_identity_half

/-- At `z = 1/2`, the Dirichlet kernel norm is bounded by the Hardy kernel norm. -/
example : ‖dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ ^ 2 ≤ 4 / 3 := by
  have h := norm_sq_dirichletKernel_le_inv ((1 / 2 : ℝ) : ℂ) half_mem_disc
  rw [norm_half] at h
  have h2 : (1 : ℝ) / (1 - (1 / 2 : ℝ) ^ 2) = 4 / 3 := by norm_num
  rw [h2] at h
  exact h

/-- The pointwise bound at `1/2`, in closed form. -/
example (a : ℓ²(ℕ, ℂ)) :
    ‖dirichletEval ((1 / 2 : ℝ) : ℂ) half_mem_disc a‖ ≤
      ‖a‖ * Real.sqrt (4 * Real.log (4 / 3)) := by
  calc ‖dirichletEval ((1 / 2 : ℝ) : ℂ) half_mem_disc a‖ ≤
        ‖a‖ * ‖dirichletKernel ((1 / 2 : ℝ) : ℂ) half_mem_disc‖ :=
        norm_dirichletEval_le _ _ a
    _ = ‖a‖ * Real.sqrt (4 * Real.log (4 / 3)) := by
        rw [norm_dirichletKernel_of_ne_zero _ half_mem_disc (by simp), norm_half,
          log_identity_half]

/-- The Taylor series of a `𝒟` function converges absolutely at `1/2`. -/
example (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * (((1 / 2 : ℝ) : ℂ)) ^ n /
      (Real.sqrt ((n : ℝ) + 1) : ℂ)) :=
  summable_dirichletEval_terms ((1 / 2 : ℝ) : ℂ) half_mem_disc a

end MathlibExtTest.Analysis.InnerProductSpace.DirichletSpaceTests
