/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.BasisLorentzian
import Mathlib.Combinatorics.Matroid.Map

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

-- Rank three with a loop: on `Fin 5`, the elements `2` and `3` are parallel and `4` is a loop,
-- so the bases are `{0, 1, 2}` and `{0, 1, 3}`. The derivative in `X 4` vanishes, and the
-- derivative in each other variable is the basis generating polynomial of a contraction.
private noncomputable def loopRankThree : _root_.Matroid (Fin 5) :=
  (Matroid.uniqueBaseOn ({0, 1, 2} : Set (Fin 4)) Set.univ).comap ![0, 1, 2, 2, 3]

-- The element `4` lies in the ground set and is a loop.
example : loopRankThree.IsLoop 4 := by
  rw [← Matroid.singleton_dep, loopRankThree, Matroid.comap_dep_iff]
  simp

private lemma loopRankThree_isBase_iff (B : Finset (Fin 5)) :
    loopRankThree.IsBase (B : Set (Fin 5)) ↔ B = {0, 1, 2} ∨ B = {0, 1, 3} := by
  have hsurj : Function.Surjective (![0, 1, 2, 2, 3] : Fin 5 → Fin 4) := by decide
  rw [loopRankThree, Matroid.comap_isBase_iff, Matroid.uniqueBaseOn_ground,
    Set.image_preimage_eq _ hsurj, Matroid.uniqueBaseOn_isBasis_iff subset_rfl, Set.univ_inter,
    ← Finset.coe_image, ← Finset.card_image_iff, Set.preimage_univ]
  simp only [Set.subset_univ, and_true]
  rw [show ({0, 1, 2} : Set (Fin 4)) = (({0, 1, 2} : Finset (Fin 4)) : Set (Fin 4)) by simp,
    Finset.coe_inj]
  revert B
  decide

example : (⟨X 0 * X 1 * X 2 + X 0 * X 1 * X 3,
    (((isHomogeneous_X ℝ 0).mul (isHomogeneous_X ℝ 1)).mul (isHomogeneous_X ℝ 2)).add
      (((isHomogeneous_X ℝ 0).mul (isHomogeneous_X ℝ 1)).mul (isHomogeneous_X ℝ 3))⟩ :
    H 5 3) ∈ L 5 3 := by
  classical
  apply basisGeneratingPolynomial_mem_L loopRankThree
  · have hB := ((loopRankThree_isBase_iff {0, 1, 2}).mpr (Or.inl rfl)).encard_eq_eRank
    rw [← hB, Set.encard_coe_eq_coe_finsetCard]
    rfl
  · have hs : Finset.univ.filter (fun B : Finset (Fin 5) =>
        loopRankThree.IsBase (B : Set (Fin 5))) = {{0, 1, 2}, {0, 1, 3}} := by
      ext B
      simp [loopRankThree_isBase_iff]
    have h012 : indicatorVec ({0, 1, 2} : Finset (Fin 5)) =
        single 0 1 + single 1 1 + single 2 1 := by
      ext i
      fin_cases i <;> simp [indicatorVec_apply]
    have h013 : indicatorVec ({0, 1, 3} : Finset (Fin 5)) =
        single 0 1 + single 1 1 + single 3 1 := by
      ext i
      fin_cases i <;> simp [indicatorVec_apply]
    rw [hs, Finset.sum_pair (by decide), h012, h013, show (1 : ℝ) = 1 * 1 * 1 by norm_num,
      ← monomial_mul_monomial, ← monomial_mul_monomial, ← monomial_mul_monomial,
      ← monomial_mul_monomial, monomial_single_one, monomial_single_one, monomial_single_one,
      monomial_single_one]

end MathlibExt.Combinatorics.LorentzianToolboxWanted.BasisLorentzianTest
