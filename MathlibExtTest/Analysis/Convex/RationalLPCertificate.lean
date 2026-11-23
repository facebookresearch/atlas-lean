/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

meta import MathlibExt.Analysis.Convex.RationalLPCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

namespace MathlibExtTest.Analysis.Convex.RationalLPCertificate

open MathlibExt.Analysis.Convex.RationalLPCertificate

open scoped Matrix

-- Transport fixtures: two suppliers (3/2, 1/2), two customers (1, 1),
-- costs (1, 3, 2, 1) in row-major order, negative shipping cost maximized.
def A8x4 : Matrix (Fin 8) (Fin 4) ℚ :=
  ![![1, 1, 0, 0],
    ![-1, -1, 0, 0],
    ![0, 0, 1, 1],
    ![0, 0, -1, -1],
    ![1, 0, 1, 0],
    ![-1, 0, -1, 0],
    ![0, 1, 0, 1],
    ![0, -1, 0, -1]]

def b8 : Fin 8 → ℚ := ![3/2, -3/2, 1/2, -1/2, 1, -1, 1, -1]

def c4 : Fin 4 → ℚ := ![-1, -3, -2, -1]

def y8 : Fin 8 → ℚ := ![0, 1, 1, 0, 0, 0, 0, 2]

def xExact : Fin 4 → ℚ := ![1, 1/2, 0, 1/2]

def xLoose : Fin 4 → ℚ := ![11/12, 7/12, 1/12, 5/12]

def xPert : Fin 4 → ℚ := ![1001/1000, 1/2, 0, 1/2]

-- Minimal 1x1 fixtures isolating one failing predicate each.
def A1nz : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]

def A1z : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]

def v1z : Fin 1 → ℚ := ![0]

def v1o : Fin 1 → ℚ := ![1]

def v1n : Fin 1 → ℚ := ![-1]

-- Empty-shape fixtures for partially empty dimensions.
def A01 : Matrix (Fin 0) (Fin 1) ℚ := ![]

def A10 : Matrix (Fin 1) (Fin 0) ℚ := ![![]]

def A00 : Matrix (Fin 0) (Fin 0) ℚ := ![]

def v0 : Fin 0 → ℚ := ![]

-- Exact and loose objective values over ℚ.
theorem exact_primal_obj : dotProduct c4 xExact = (-3 : ℚ) := by
  simp [dotProduct, c4, xExact, Fin.sum_univ_four]
  norm_num

theorem exact_dual_obj : dotProduct b8 y8 = (-3 : ℚ) := by
  simp [dotProduct, b8, y8, Fin.sum_univ_eight]
  norm_num

theorem loose_primal_obj : dotProduct c4 xLoose = (-13/4 : ℚ) := by
  simp [dotProduct, c4, xLoose, Fin.sum_univ_four]
  norm_num

theorem exact_gap_eq : dotProduct b8 y8 - dotProduct c4 xExact = (0 : ℚ) := by
  rw [exact_dual_obj, exact_primal_obj]
  norm_num

theorem loose_gap_eq : dotProduct b8 y8 - dotProduct c4 xLoose = (1/4 : ℚ) := by
  rw [exact_dual_obj, loose_primal_obj]
  norm_num

-- Cast objective values over ℝ for the real APIs.
theorem exact_primal_obj_real :
    dotProduct (fun (i : Fin 4) => (c4 i : ℝ))
      (fun (i : Fin 4) => ((xExact i : ℚ) : ℝ)) = (-3 : ℝ) := by
  simp [dotProduct, c4, xExact, Fin.sum_univ_four]
  norm_num

theorem exact_dual_obj_real :
    dotProduct (fun (j : Fin 8) => (b8 j : ℝ))
      (fun (j : Fin 8) => ((y8 j : ℚ) : ℝ)) = (-3 : ℝ) := by
  simp [dotProduct, b8, y8, Fin.sum_univ_eight]
  norm_num

theorem loose_primal_obj_real :
    dotProduct (fun (i : Fin 4) => (c4 i : ℝ))
      (fun (i : Fin 4) => ((xLoose i : ℚ) : ℝ)) = (-13/4 : ℝ) := by
  simp [dotProduct, c4, xLoose, Fin.sum_univ_four]
  norm_num

-- Exact accept at zero gap.
theorem exact_accept :
    checksLPGap 8 4 A8x4 b8 c4 xExact y8 (0 : ℚ) = true := by
  rw [checksLPGap_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [xExact]
  · intro j
    fin_cases j <;>
      simp [A8x4, xExact, b8, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  · intro j; fin_cases j <;> simp [y8]
  · intro i
    fin_cases i <;>
      simp [A8x4, y8, c4, Matrix.mulVec, dotProduct, Matrix.transpose,
        Fin.sum_univ_eight] <;>
      norm_num
  · rw [exact_gap_eq]
  · rw [exact_gap_eq]

-- Loose accept at gap 1/4.
theorem loose_accept :
    checksLPGap 8 4 A8x4 b8 c4 xLoose y8 (1/4 : ℚ) = true := by
  rw [checksLPGap_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [xLoose] <;> norm_num
  · intro j
    fin_cases j <;>
      simp [A8x4, xLoose, b8, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  · intro j; fin_cases j <;> simp [y8]
  · intro i
    fin_cases i <;>
      simp [A8x4, y8, c4, Matrix.mulVec, dotProduct, Matrix.transpose,
        Fin.sum_univ_eight] <;>
      norm_num
  · rw [loose_gap_eq]; norm_num
  · rw [loose_gap_eq]

-- Zero-dimension accept.
theorem zero_accept :
    checksLPGap 0 0 A00 v0 v0 v0 v0 (0 : ℚ) = true := by
  rw [checksLPGap_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro i; exact i.elim0
  · simp [dotProduct, v0]
  · simp [dotProduct, v0]

-- m=0, n=1 accept: dual row 0 ≤ 0 still holds.
theorem m01_accept :
    checksLPGap 0 1 A01 v0 v1z v1z v0 (0 : ℚ) = true := by
  rw [checksLPGap_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i; simp [v1z]
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro i
    fin_cases i
    simp [A01, v0, v1z, Matrix.mulVec, dotProduct, Matrix.transpose]
  · simp [dotProduct, v0, v1z]
  · simp [dotProduct, v0, v1z]

-- m=1, n=0 accept: primal row 0 ≤ 0 still holds.
theorem m10_accept :
    checksLPGap 1 0 A10 v1z v0 v0 v1z (0 : ℚ) = true := by
  rw [checksLPGap_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro j
    fin_cases j
    simp [A10, v0, v1z, Matrix.mulVec, dotProduct]
  · intro j; fin_cases j; simp [v1z]
  · intro i; exact i.elim0
  · simp [dotProduct, v0, v1z]
  · simp [dotProduct, v0, v1z]

-- Loose reject at gap 1/5: true gap 1/4 exceeds budget.
theorem loose_reject :
    checksLPGap 8 4 A8x4 b8 c4 xLoose y8 (1/5 : ℚ) = false := by
  have hne : ¬(checksLPGap 8 4 A8x4 b8 c4 xLoose y8 (1/5 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, _, _, _, _, hle⟩ := h
    rw [loose_gap_eq] at hle
    norm_num at hle
  rw [Bool.eq_false_iff]
  exact hne

-- Perturbation reject: 1001/1000 breaks the first supply row.
theorem pert_reject :
    checksLPGap 8 4 A8x4 b8 c4 xPert y8 (1 : ℚ) = false := by
  have hne : ¬(checksLPGap 8 4 A8x4 b8 c4 xPert y8 (1 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, hAx, _, _, _, _⟩ := h
    have h0 := hAx ⟨0, by norm_num⟩
    simp [A8x4, xPert, b8, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- Negative epsilon rejects even the exact certificate.
theorem exact_neg_eps_reject :
    checksLPGap 8 4 A8x4 b8 c4 xExact y8 (-1 : ℚ) = false := by
  have hne : ¬(checksLPGap 8 4 A8x4 b8 c4 xExact y8 (-1 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, _, _, _, _, hle⟩ := h
    rw [exact_gap_eq] at hle
    norm_num at hle
  rw [Bool.eq_false_iff]
  exact hne

-- Zero-dimension reject with negative epsilon.
theorem zero_neg_eps_reject :
    checksLPGap 0 0 A00 v0 v0 v0 v0 (-1 : ℚ) = false := by
  have hne : ¬(checksLPGap 0 0 A00 v0 v0 v0 v0 (-1 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, _, _, _, _, hle⟩ := h
    simp [dotProduct, v0] at hle
    norm_num at hle
  rw [Bool.eq_false_iff]
  exact hne

-- Isolated 1x1 guard: negative primal coordinate.
theorem guard_neg_primal :
    checksLPGap 1 1 A1nz v1z v1z v1n v1z (0 : ℚ) = false := by
  have hne : ¬(checksLPGap 1 1 A1nz v1z v1z v1n v1z (0 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨hx0, _, _, _, _, _⟩ := h
    have h0 := hx0 ⟨0, by norm_num⟩
    simp [v1n] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- Isolated 1x1 guard: violated primal row.
theorem guard_viol_primal_row :
    checksLPGap 1 1 A1nz v1z v1z v1o v1z (0 : ℚ) = false := by
  have hne : ¬(checksLPGap 1 1 A1nz v1z v1z v1o v1z (0 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, hAx, _, _, _, _⟩ := h
    have h0 := hAx ⟨0, by norm_num⟩
    simp [A1nz, v1o, v1z, Matrix.mulVec, dotProduct] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- Isolated 1x1 guard: negative dual coordinate.
theorem guard_neg_dual :
    checksLPGap 1 1 A1z v1z v1z v1z v1n (0 : ℚ) = false := by
  have hne : ¬(checksLPGap 1 1 A1z v1z v1z v1z v1n (0 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, _, hy0, _, _, _⟩ := h
    have h0 := hy0 ⟨0, by norm_num⟩
    simp [v1n] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- Isolated 1x1 guard: violated dual row.
theorem guard_viol_dual_row :
    checksLPGap 1 1 A1z v1z v1o v1z v1z (0 : ℚ) = false := by
  have hne : ¬(checksLPGap 1 1 A1z v1z v1o v1z v1z (0 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, _, _, hAty, _, _⟩ := h
    have h0 := hAty ⟨0, by norm_num⟩
    simp [A1z, v1o, v1z, Matrix.mulVec, dotProduct, Matrix.transpose] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- m=0, n=1 reject: positive c breaks the dual row.
theorem m01_reject :
    checksLPGap 0 1 A01 v0 v1o v1z v0 (0 : ℚ) = false := by
  have hne : ¬(checksLPGap 0 1 A01 v0 v1o v1z v0 (0 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, _, _, hAty, _, _⟩ := h
    have h0 := hAty ⟨0, by norm_num⟩
    simp [A01, v0, v1o, Matrix.mulVec, dotProduct, Matrix.transpose] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- m=1, n=0 reject: negative b breaks the 0 ≤ b row.
theorem m10_reject :
    checksLPGap 1 0 A10 v1n v0 v0 v1z (0 : ℚ) = false := by
  have hne : ¬(checksLPGap 1 0 A10 v1n v0 v0 v1z (0 : ℚ) = true) := by
    rw [checksLPGap_eq_true_iff]
    intro h
    obtain ⟨_, hAx, _, _, _, _⟩ := h
    have h0 := hAx ⟨0, by norm_num⟩
    simp [A10, v0, v1n, Matrix.mulVec, dotProduct] at h0
    norm_num at h0
  rw [Bool.eq_false_iff]
  exact hne

-- Exact primal optimality over ℝ for arbitrary feasible competitors.
theorem exact_primal_optimal : ∀ (x' : Fin 4 → ℝ), (∀ i, 0 ≤ x' i) →
    (∀ j,
      (Matrix.mulVec (Matrix.map A8x4 (fun (q : ℚ) => (q : ℝ))) x') j ≤
        (b8 j : ℝ)) →
    dotProduct (fun (i : Fin 4) => (c4 i : ℝ)) x' ≤ (-3 : ℝ) := by
  intro x' hx' hAx'
  have hopt := optimal_of_checks_zero 8 4 A8x4 b8 c4 xExact y8 exact_accept
  obtain ⟨_, _, hprimal, _⟩ := hopt
  have hle := hprimal x' hx' hAx'
  rw [exact_primal_obj_real] at hle
  exact hle

-- Exact dual optimality over ℝ for arbitrary feasible competitors.
theorem exact_dual_optimal : ∀ (y' : Fin 8 → ℝ), (∀ j, 0 ≤ y' j) →
    (∀ i,
      (c4 i : ℝ) ≤
        (Matrix.mulVec
            (Matrix.transpose (Matrix.map A8x4 (fun (q : ℚ) => (q : ℝ)))) y')
          i) →
    (-3 : ℝ) ≤ dotProduct (fun (j : Fin 8) => (b8 j : ℝ)) y' := by
  intro y' hy' hAty'
  have hopt := optimal_of_checks_zero 8 4 A8x4 b8 c4 xExact y8 exact_accept
  obtain ⟨_, _, _, hdual⟩ := hopt
  have hle := hdual y' hy' hAty'
  rw [exact_dual_obj_real] at hle
  exact hle

-- Minimum shipping cost 3 for arbitrary feasible real shippers.
theorem min_shipping_cost_three : ∀ (z : Fin 4 → ℝ), (∀ i, 0 ≤ z i) →
    (∀ j,
      (Matrix.mulVec (Matrix.map A8x4 (fun (q : ℚ) => (q : ℝ))) z) j ≤
        (b8 j : ℝ)) →
    (3 : ℝ) ≤ -(dotProduct (fun (i : Fin 4) => (c4 i : ℝ)) z) := by
  intro z hz0 hAz
  have hopt := optimal_of_checks_zero 8 4 A8x4 b8 c4 xExact y8 exact_accept
  obtain ⟨_, _, hprimal, _⟩ := hopt
  have hle := hprimal z hz0 hAz
  rw [exact_primal_obj_real] at hle
  have h3 : (3 : ℝ) = -(-3 : ℝ) := by norm_num
  rw [h3]
  exact neg_le_neg hle

-- Loose soundness bound over ℝ: -13/4 + 1/4 = -3.
theorem loose_sound_bound : ∀ (z : Fin 4 → ℝ), (∀ i, 0 ≤ z i) →
    (∀ j,
      (Matrix.mulVec (Matrix.map A8x4 (fun (q : ℚ) => (q : ℝ))) z) j ≤
        (b8 j : ℝ)) →
    dotProduct (fun (i : Fin 4) => (c4 i : ℝ)) z ≤ (-3 : ℝ) := by
  intro z hz0 hAz
  have hsound :=
    real_feasible_and_gap_le_of_checks 8 4 A8x4 b8 c4 xLoose y8 (1/4 : ℚ)
      loose_accept
  obtain ⟨_, _, _, hbound⟩ := hsound
  have hle := hbound z hz0 hAz
  rw [loose_primal_obj_real] at hle
  norm_num at hle
  exact hle

-- Dimension mismatch is a type error, not a runtime rejection.
-- Positive control is exact_accept above. Negative control fails elaboration
-- on the Fin 8 vector b8 where a Fin 4 primal is expected; mutating b8 to
-- xExact makes the inner have succeed, so fail_if_success fails.
example : True := by
  fail_if_success
    (have h : checksLPGap 8 4 A8x4 b8 c4 b8 y8 (0 : ℚ) = true := exact_accept)
  trivial

-- Evaluators: original six first, then empty-shape and guard pins.
#eval checksLPGap 8 4 A8x4 b8 c4 xExact y8 (0 : ℚ)
#eval checksLPGap 8 4 A8x4 b8 c4 xLoose y8 (1/4 : ℚ)
#eval checksLPGap 8 4 A8x4 b8 c4 xLoose y8 (1/5 : ℚ)
#eval checksLPGap 8 4 A8x4 b8 c4 xPert y8 (1 : ℚ)
#eval checksLPGap 8 4 A8x4 b8 c4 xExact y8 (-1 : ℚ)
#eval checksLPGap 0 0 A00 v0 v0 v0 v0 (0 : ℚ)
#eval checksLPGap 0 0 A00 v0 v0 v0 v0 (-1 : ℚ)
#eval checksLPGap 0 1 A01 v0 v1z v1z v0 (0 : ℚ)
#eval checksLPGap 0 1 A01 v0 v1o v1z v0 (0 : ℚ)
#eval checksLPGap 1 0 A10 v1z v0 v0 v1z (0 : ℚ)
#eval checksLPGap 1 0 A10 v1n v0 v0 v1z (0 : ℚ)
#eval checksLPGap 1 1 A1nz v1z v1z v1n v1z (0 : ℚ)
#eval checksLPGap 1 1 A1nz v1z v1z v1o v1z (0 : ℚ)
#eval checksLPGap 1 1 A1z v1z v1z v1z v1n (0 : ℚ)
#eval checksLPGap 1 1 A1z v1z v1o v1z v1z (0 : ℚ)

#print axioms checksLPGap
#print axioms checksLPGap_eq_true_iff
#print axioms real_feasible_and_gap_le_of_checks
#print axioms optimal_of_checks_zero

end MathlibExtTest.Analysis.Convex.RationalLPCertificate
