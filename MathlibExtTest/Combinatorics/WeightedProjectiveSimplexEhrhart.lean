/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexEhrhart
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Tests for Ehrhart counts and unimodality -/

open MetaMathlibExt Polynomial

-- The zeroth dilate of any nonempty set contains just the origin.
example {d : ℕ} (P : Set (Fin d → ℝ)) (hP : P.Nonempty) : ehrhart P 0 = 1 := by
  obtain ⟨y, hy⟩ := hP
  have h : {x : Fin d → ℤ | IsLatticePoint (polytopeDilate 0 P) x} = {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, IsLatticePoint, polytopeDilate,
      Nat.cast_zero, zero_mul]
    constructor
    · rintro ⟨_, _, hx⟩
      funext i
      change x i = 0
      have hi : (x i : ℝ) = 0 := congrFun hx i
      exact_mod_cast hi
    · rintro rfl
      exact ⟨y, hy, by simp⟩
  rw [ehrhart, h, Set.ncard_singleton]

-- Infinite lattice-point sets are assigned the count zero.
example : ehrhart (Set.univ : Set (Fin 1 → ℝ)) 1 = 0 := by
  have h : {x : Fin 1 → ℤ | IsLatticePoint (polytopeDilate 1 Set.univ) x} =
      Set.univ := by
    simp [polytopeDilate_one, IsLatticePoint]
  rw [ehrhart, h, Set.infinite_univ.ncard]

-- The peak is at the middle coefficient.
example : IsUnimodal (1 + 2 * X + X ^ 2 : Polynomial ℤ) := by
  let p : Polynomial ℤ := 1 + 2 * X + X ^ 2
  have h₂ : p.coeff 2 ≠ 0 := by
    norm_num only [p, coeff_add, coeff_one, coeff_X_pow, coeff_X, coeff_ofNat_mul,
      ite_true, ite_false]
  have hdeg : p.natDegree ≤ 2 := natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    have h0 : n ≠ 0 := by omega
    have h1 : 1 ≠ n := by omega
    have h2 : n ≠ 2 := by omega
    simp only [p, coeff_add, coeff_one, coeff_X_pow, coeff_X, coeff_ofNat_mul,
      ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, mul_zero, add_zero]
  refine ⟨1, (by decide : 1 ≤ 2).trans (le_natDegree_of_ne_zero h₂), ?_, ?_⟩
  · intro i j hij hj
    interval_cases j <;> interval_cases i <;>
      norm_num only [p, coeff_add, coeff_one, coeff_X_pow, coeff_X, coeff_ofNat_mul,
        ite_true, ite_false]
  · intro i j hi hij hj
    have hj₂ := hj.trans hdeg
    interval_cases j <;> interval_cases i <;>
      norm_num only [p, coeff_add, coeff_one, coeff_X_pow, coeff_X, coeff_ofNat_mul,
        ite_true, ite_false]

example : IsUnimodal (0 : Polynomial ℤ) :=
  ⟨0, Nat.zero_le _, by simp, by simp⟩

-- A strict dip cannot occur on either side of the peak.
example : ¬ IsUnimodal (2 + X + 2 * X ^ 2 : Polynomial ℤ) := by
  let p : Polynomial ℤ := 2 + X + 2 * X ^ 2
  have h₂ : p.coeff 2 ≠ 0 := by
    norm_num only [p, coeff_add, coeff_ofNat_succ, coeff_X_pow, coeff_X, coeff_ofNat_mul,
      ite_true, ite_false]
  rintro ⟨t, _, hinc, hdec⟩
  by_cases ht : 1 ≤ t
  · have h := hinc 0 1 (by decide) ht
    norm_num only [p, coeff_add, coeff_ofNat_zero, coeff_ofNat_succ, coeff_X_pow, coeff_X,
      coeff_ofNat_mul, ite_true, ite_false] at h
  · have h := hdec 1 2 (by omega) (by decide) (le_natDegree_of_ne_zero h₂)
    norm_num only [p, coeff_add, coeff_ofNat_succ, coeff_X_pow, coeff_X, coeff_ofNat_mul,
      ite_true, ite_false] at h
