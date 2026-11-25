/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.BasisLorentzian

open Finsupp MvPolynomial
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials
open MathlibExt.Combinatorics.Matroid.MConvex

namespace MathlibExt.Combinatorics.LorentzianToolboxWanted.BasisLorentzianTest

private lemma indicatorVec_empty {α : Type*} : indicatorVec (∅ : Finset α) = 0 := by
  classical ext; simp [indicatorVec_apply]

private lemma monomial_single_one {n : ℕ} (i : Fin n) :
    monomial (single i 1) (1 : ℝ) = X i := by
  rw [← X_pow_eq_monomial]
  simp

private lemma indicatorVec_univ_two :
    indicatorVec (Finset.univ : Finset (Fin 2)) = single 0 1 + single 1 1 := by
  ext i
  fin_cases i <;> simp [indicatorVec_apply]

-- The free matroid on two elements: the only base is `{0, 1}`.
example : (⟨X 0 * X 1, (isHomogeneous_X ℝ 0).mul (isHomogeneous_X ℝ 1)⟩ :
    H 2 2) ∈ L 2 2 := by
  classical
  apply basisGeneratingPolynomial_mem_L (Matroid.freeOn (Set.univ : Set (Fin 2)))
  · simp [Matroid.eRank_freeOn]
  · have hs : Finset.univ.filter (fun B : Finset (Fin 2) =>
        (Matroid.freeOn (Set.univ : Set (Fin 2))).IsBase (B : Set (Fin 2))) =
        {Finset.univ} := by
      ext B
      simp [Finset.mem_singleton]
    rw [hs, Finset.sum_singleton, indicatorVec_univ_two]
    rw [show (1 : ℝ) = 1 * 1 from (mul_one 1).symm, ← monomial_mul_monomial,
      monomial_single_one, monomial_single_one]

-- A matroid whose ground set is `{0}`: the only base is `{0}`, and the other
-- variable does not appear.
example : (⟨X 0, isHomogeneous_X ℝ 0⟩ : H 2 1) ∈ L 2 1 := by
  classical
  apply basisGeneratingPolynomial_mem_L (Matroid.freeOn ({0} : Set (Fin 2)))
  · simp [Matroid.eRank_freeOn]
  · have hs : Finset.univ.filter (fun B : Finset (Fin 2) =>
        (Matroid.freeOn ({0} : Set (Fin 2))).IsBase (B : Set (Fin 2))) =
        {{0}} := by
      ext B
      simp [Finset.mem_singleton]
    rw [hs, Finset.sum_singleton]
    have hind : indicatorVec ({0} : Finset (Fin 2)) = single 0 1 := by
      ext i
      fin_cases i <;> simp [indicatorVec_apply]
    rw [hind, monomial_single_one]

-- All loops: the only base is empty, of rank `0`, even with `n > 0`.
example : (⟨1, isHomogeneous_one (Fin 2) ℝ⟩ : H 2 0) ∈ L 2 0 := by
  classical
  apply basisGeneratingPolynomial_mem_L (Matroid.loopyOn (Set.univ : Set (Fin 2)))
  · simp [Matroid.eRank_loopyOn]
  · have hs : Finset.univ.filter (fun B : Finset (Fin 2) =>
        (Matroid.loopyOn (Set.univ : Set (Fin 2))).IsBase (B : Set (Fin 2))) =
        {∅} := by
      ext B
      simp [Finset.mem_singleton]
    rw [hs, Finset.sum_singleton, indicatorVec_empty]
    simp

end MathlibExt.Combinatorics.LorentzianToolboxWanted.BasisLorentzianTest
