/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Ecology.Leslie
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Defs

import MathlibExt.Biology.Demography.Leslie
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.NeZero
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for stable-age convergence of primitive Leslie matrices

Checks the Strong Ergodic Theorem on two concrete 2-age fixtures with
growth rates `r = 1` and `r = 3/2`, the finite-step projection identity,
existence of the stable age distribution, and failure of convergence for
a periodic (imprimitive) Leslie matrix.
-/
@[expose] public section

namespace MathlibExtTest.Biology.Demography.Leslie

open Matrix Filter Topology
open MathlibExt.Biology.Ecology.Leslie
open MathlibExt.Biology.Demography.Leslie

/-- Fertility row for the `r = 1` fixture. -/
noncomputable def f_r1 : Fin 2 → ℝ := ![1/2, 1/2]

/-- Survival column for the `r = 1` fixture. -/
noncomputable def s_r1 : Fin 2 → ℝ := ![1, 1]

/-- Right eigenvector for the `r = 1` fixture. -/
noncomputable def v_r1 : Fin 2 → ℝ := ![1, 1]

/-- Fertility row for the `r = 3/2` fixture. -/
noncomputable def f_r32 : Fin 2 → ℝ := ![1, 3/4]

/-- Survival column for the `r = 3/2` fixture. -/
noncomputable def s_r32 : Fin 2 → ℝ := ![1, 1]

/-- Right eigenvector for the `r = 3/2` fixture. -/
noncomputable def v_r32 : Fin 2 → ℝ := ![3, 2]

/-- Left eigenvector shared by both fixtures. -/
noncomputable def w_lr : Fin 2 → ℝ := ![2, 1]

/-- Initial population for the `r = 1` fixture. -/
noncomputable def x0_r1 : Fin 2 → ℝ := ![1, 1]

/-- Initial population for the `r = 3/2` fixture. -/
noncomputable def x0_r32 : Fin 2 → ℝ := ![1, 1]

/-- Fertility row for the periodic fixture. -/
noncomputable def f_per : Fin 2 → ℝ := ![0, 1]

/-- Survival column for the periodic fixture. -/
noncomputable def s_per : Fin 2 → ℝ := ![1, 1]

/-- Initial population for the periodic fixture. -/
noncomputable def x0per : Fin 2 → ℝ := ![1, 0]

private theorem hv_r1 : ∀ i, 0 < v_r1 i := by
  intro i
  fin_cases i <;> simp [v_r1]

private theorem hw_lr : ∀ i, 0 < w_lr i := by
  intro i
  fin_cases i <;> simp [w_lr]

private theorem hv_r32 : ∀ i, 0 < v_r32 i := by
  intro i
  fin_cases i <;> simp [v_r32]

private theorem hLv_r1 : leslieMatrix f_r1 s_r1 *ᵥ v_r1 = (1 : ℝ) • v_r1 := by
  ext i
  fin_cases i <;>
    simp [leslieMatrix, f_r1, s_r1, v_r1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]; norm_num

private theorem hwL_r1 : w_lr ᵥ* leslieMatrix f_r1 s_r1 = (1 : ℝ) • w_lr := by
  ext j
  fin_cases j <;>
    simp [leslieMatrix, f_r1, s_r1, w_lr, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]; norm_num

private theorem hLv_r32 :
    leslieMatrix f_r32 s_r32 *ᵥ v_r32 = (3/2 : ℝ) • v_r32 := by
  ext i
  fin_cases i <;>
    simp [leslieMatrix, f_r32, s_r32, v_r32, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]; norm_num

private theorem hwL_r32 :
    w_lr ᵥ* leslieMatrix f_r32 s_r32 = (3/2 : ℝ) • w_lr := by
  ext j
  fin_cases j <;>
    simp [leslieMatrix, f_r32, s_r32, w_lr, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> norm_num

private theorem hprim_r1 : (leslieMatrix f_r1 s_r1).IsPrimitive := by
  rw [Matrix.isPrimitive_iff]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [leslieMatrix, f_r1, s_r1]
  · refine ⟨2, by norm_num, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [leslieMatrix, f_r1, s_r1, pow_two, Matrix.mul_apply,
        Fin.sum_univ_two]; norm_num

private theorem hprim_r32 : (leslieMatrix f_r32 s_r32).IsPrimitive := by
  rw [Matrix.isPrimitive_iff]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [leslieMatrix, f_r32, s_r32]; norm_num
  · refine ⟨2, by norm_num, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [leslieMatrix, f_r32, s_r32, pow_two, Matrix.mul_apply,
        Fin.sum_univ_two]; norm_num

private theorem hx0_r1 : ∀ i, 0 ≤ x0_r1 i := by
  intro i
  fin_cases i <;> simp [x0_r1]

private theorem hx0_r1_ne : x0_r1 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [x0_r1] at h0

private theorem hx0_r32 : ∀ i, 0 ≤ x0_r32 i := by
  intro i
  fin_cases i <;> simp [x0_r32]

private theorem hx0_r32_ne : x0_r32 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [x0_r32] at h0

private theorem hsq_per : leslieMatrix f_per s_per ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leslieMatrix, f_per, s_per, pow_two, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem hnotprim_per :
    ¬ (leslieMatrix f_per s_per).IsPrimitive := by
  rw [Matrix.isPrimitive_iff]
  rintro ⟨-, k, _, hk⟩
  have hmul : leslieMatrix f_per s_per * leslieMatrix f_per s_per = 1 := by
    rw [← pow_two, hsq_per]
  have hall : ∀ m, leslieMatrix f_per s_per ^ m = 1 ∨
      leslieMatrix f_per s_per ^ m = leslieMatrix f_per s_per := by
    intro m
    induction m with
    | zero => left; simp
    | succ m ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h, one_mul]
      · left; rw [pow_succ, h, hmul]
  rcases hall k with h | h
  · have h01 := hk 0 1
    rw [h] at h01
    simp at h01
  · have h00 := hk 0 0
    rw [h] at h00
    simp [leslieMatrix, f_per] at h00

/-- Finite-step projection applied to the `r = 1` fixture. -/
theorem test_projection_r1 (x : ℕ → Fin 2 → ℝ)
    (hstep : ∀ t, x (t + 1) = leslieMatrix f_r1 s_r1 *ᵥ x t) :
    x 2 = (leslieMatrix f_r1 s_r1 ^ 2) *ᵥ x 0 :=
  leslie_projection f_r1 s_r1 x hstep 2

/-- Growth-rate convergence for the `r = 1` fixture. -/
theorem test_growth_r1 :
    Tendsto
      (fun t : ℕ => (leslieMatrix f_r1 s_r1 ^ t *ᵥ x0_r1) 0 / (1 : ℝ) ^ t)
      atTop (𝓝 (w_lr ⬝ᵥ x0_r1 / (w_lr ⬝ᵥ v_r1) * v_r1 0)) :=
  tendsto_leslieMatrix_pow_mulVec_div_pow hprim_r1 (by norm_num : (0:ℝ) < 1)
    hv_r1 hw_lr hLv_r1 hwL_r1 x0_r1 0

/-- Growth-rate convergence for the `r = 3/2` fixture. -/
theorem test_growth_r32 :
    Tendsto
      (fun t : ℕ =>
        (leslieMatrix f_r32 s_r32 ^ t *ᵥ x0_r32) 0 / (3/2 : ℝ) ^ t)
      atTop (𝓝 (w_lr ⬝ᵥ x0_r32 / (w_lr ⬝ᵥ v_r32) * v_r32 0)) :=
  tendsto_leslieMatrix_pow_mulVec_div_pow hprim_r32
    (by norm_num : (0:ℝ) < 3/2) hv_r32 hw_lr hLv_r32 hwL_r32 x0_r32 0

/-- Age-distribution convergence for the `r = 1` fixture. -/
theorem test_age_r1 :
    Tendsto
      (fun t : ℕ => (leslieMatrix f_r1 s_r1 ^ t *ᵥ x0_r1) 0 /
        ∑ j, (leslieMatrix f_r1 s_r1 ^ t *ᵥ x0_r1) j)
      atTop (𝓝 (v_r1 0 / ∑ j, v_r1 j)) :=
  tendsto_leslie_age_distribution hprim_r1 (by norm_num : (0:ℝ) < 1) hv_r1
    hw_lr hLv_r1 hwL_r1 hx0_r1 hx0_r1_ne 0

/-- Age-distribution convergence for the `r = 3/2` fixture. -/
theorem test_age_r32 :
    Tendsto
      (fun t : ℕ => (leslieMatrix f_r32 s_r32 ^ t *ᵥ x0_r32) 0 /
        ∑ j, (leslieMatrix f_r32 s_r32 ^ t *ᵥ x0_r32) j)
      atTop (𝓝 (v_r32 0 / ∑ j, v_r32 j)) :=
  tendsto_leslie_age_distribution hprim_r32 (by norm_num : (0:ℝ) < 3/2)
    hv_r32 hw_lr hLv_r32 hwL_r32 hx0_r32 hx0_r32_ne 0

/-- Stable age distribution exists for the `r = 1` fixture. -/
theorem test_exists_r1 :
    ∃ (r : ℝ) (v : Fin 2 → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ ∑ i, v i = 1 ∧
      leslieMatrix f_r1 s_r1 *ᵥ v = r • v ∧
      ∀ x₀ : Fin 2 → ℝ, (∀ i, 0 ≤ x₀ i) → x₀ ≠ 0 → ∀ i,
        Tendsto (fun t : ℕ => (leslieMatrix f_r1 s_r1 ^ t *ᵥ x₀) i /
          ∑ j, (leslieMatrix f_r1 s_r1 ^ t *ᵥ x₀) j) atTop (𝓝 (v i)) := by
  have : NeZero 2 := ⟨by norm_num⟩
  exact exists_stable_age_distribution hprim_r1

/-- The periodic swap matrix is not primitive. -/
theorem test_periodic_not_primitive :
    ¬ (leslieMatrix f_per s_per).IsPrimitive :=
  hnotprim_per

private theorem share_per_even (m : ℕ) :
    (leslieMatrix f_per s_per ^ (2 * m) *ᵥ x0per) 0 /
      ∑ j, (leslieMatrix f_per s_per ^ (2 * m) *ᵥ x0per) j = 1 := by
  rw [pow_mul, hsq_per, one_pow]
  simp [x0per, Matrix.one_mulVec, Fin.sum_univ_two]

private theorem share_per_odd (m : ℕ) :
    (leslieMatrix f_per s_per ^ (2 * m + 1) *ᵥ x0per) 0 /
      ∑ j, (leslieMatrix f_per s_per ^ (2 * m + 1) *ᵥ x0per) j = 0 := by
  rw [pow_succ, pow_mul, hsq_per, one_pow, one_mul]
  simp [leslieMatrix, f_per, s_per, x0per, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Age shares have no limit for the periodic matrix: the share of age class `0` is `1`
at even times and `0` at odd times, so the two subsequences would force any limit to be
both `1` and `0`. -/
theorem test_periodic_no_limit :
    ¬ ∃ l : ℝ, Tendsto
      (fun t : ℕ => (leslieMatrix f_per s_per ^ t *ᵥ x0per) 0 /
        ∑ j, (leslieMatrix f_per s_per ^ t *ᵥ x0per) j)
      atTop (𝓝 l) := by
  rintro ⟨l, hlim⟩
  have h2m : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have h2m1 : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hl1 : l = 1 := tendsto_nhds_unique
    ((hlim.comp h2m).congr fun m => share_per_even m) tendsto_const_nhds
  have hl0 : l = 0 := tendsto_nhds_unique
    ((hlim.comp h2m1).congr fun m => share_per_odd m) tendsto_const_nhds
  exact one_ne_zero (hl1.symm.trans hl0)

/-- Age shares do not converge to `1/2`, the share at which the even-time value `1` and
the odd-time value `0` would balance, for the periodic matrix; this is the special case
`l = 1/2` of `test_periodic_no_limit`. -/
theorem test_periodic_not_tendsto_half :
    ¬ Tendsto
      (fun t : ℕ => (leslieMatrix f_per s_per ^ t *ᵥ x0per) 0 /
        ∑ j, (leslieMatrix f_per s_per ^ t *ᵥ x0per) j)
      atTop (𝓝 (1/2 : ℝ)) :=
  fun h => test_periodic_no_limit ⟨1/2, h⟩

end MathlibExtTest.Biology.Demography.Leslie
