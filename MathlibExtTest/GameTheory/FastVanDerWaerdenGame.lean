/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.FastVanDerWaerdenGame
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open MetaMathlibExt.FastVanDerWaerdenGame

-- Check both the exact type and the named arguments on the direct import.
example (S : Finset ℚ) (hS : 4 ≤ S.card) (i j i' j' : Fin S.card)
    (h : IsSymmetricOfType S i j) (h' : IsSymmetricOfType S i' j') : i = i' ∧ j = j' :=
  isSymmetricOfType_unique (S := S) (hS := hS) (i := i) (j := j) (i' := i') (j' := j')
    (h := h) (h' := h')

private def four : Finset ℚ := ([0, 1, 2, 4] : List ℚ).toFinset

private theorem four_sort : four.sort = [0, 1, 2, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- At the cardinality bound, the type (1, 3) occurs and is unique.
example (i j : Fin four.card) (h : IsSymmetricOfType four i j) :
    i = ⟨1, by decide⟩ ∧ j = ⟨3, by decide⟩ := by
  have hs : IsSymmetricOfType four ⟨1, by decide⟩ ⟨3, by decide⟩ := by
    refine ⟨by decide, 2, 0, by decide, ?_⟩
    simp only [Finset.orderEmbOfFin_apply, four_sort, Fin.getElem_fin]
    decide +kernel
  exact isSymmetricOfType_unique four (by decide) i j _ _ h hs

private def reflected : Finset ℚ := ([0, 2, 3, 4] : List ℚ).toFinset

private theorem reflected_sort : reflected.sort = [0, 2, 3, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- Its reflection is instead of type (0, 2), with zero-based indices.
example (i j : Fin reflected.card) (h : IsSymmetricOfType reflected i j) :
    i = ⟨0, by decide⟩ ∧ j = ⟨2, by decide⟩ := by
  have hs : IsSymmetricOfType reflected ⟨0, by decide⟩ ⟨2, by decide⟩ := by
    refine ⟨by decide, 1 / 2, 2, by norm_num, ?_⟩
    simp only [Finset.orderEmbOfFin_apply, reflected_sort, Fin.getElem_fin]
    decide +kernel
  exact isSymmetricOfType_unique reflected (by decide) i j _ _ h hs

private def progression : Finset ℚ := ([0, 1, 2, 3, 4] : List ℚ).toFinset

private theorem progression_sort : progression.sort = [0, 1, 2, 3, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

example (i j : Fin progression.card) (h : IsSymmetricOfType progression i j) :
    i = ⟨0, by decide⟩ ∧ j = ⟨4, by decide⟩ := by
  have hs : IsSymmetricOfType progression ⟨0, by decide⟩ ⟨4, by decide⟩ := by
    refine ⟨by decide, 1, 1, by decide, ?_⟩
    simp only [Finset.orderEmbOfFin_apply, progression_sort, Fin.getElem_fin]
    decide +kernel
  exact isSymmetricOfType_unique progression (by decide) i j _ _ h hs

-- Check the exact case disjunction, cardinality bound and named arguments.
example (S : Finset ℚ) (hS : 4 ≤ S.card) (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 0 ∧ j.val = S.card - 1) ∨ (i.val = 1 ∧ j.val = S.card - 1) ∨
      (i.val = 0 ∧ j.val = S.card - 2) :=
  isSymmetricOfType_cases (S := S) (hS := hS) (i := i) (j := j) (h := h)

private def three : Finset ℚ := ([0, 1, 2] : List ℚ).toFinset

private theorem three_sort : three.sort = [0, 1, 2] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- Below the bound, deleting the same last element can give two different types.
example : IsSymmetricOfType three ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    IsSymmetricOfType three ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  refine ⟨⟨by decide, 1, 1, by decide, ?_⟩, ⟨by decide, 2, 0, by decide, ?_⟩⟩ <;>
    simp only [Finset.orderEmbOfFin_apply, three_sort, Fin.getElem_fin] <;> decide +kernel

-- Zero-geometric type and its reflection use different rank types.
example : MakerWinsWithin ({0, 1, 2, 4} : Finset ℕ) 4 ∅ ∅ := by
  apply (makerWinsWithin_four_iff_isSymmetric _ (by decide)).2
  rw [show ({0, 1, 2, 4} : Finset ℕ).image (fun s : ℕ ↦ (s : ℚ)) = four by decide +kernel]
  refine ⟨⟨1, by decide⟩, ⟨3, by decide⟩, by decide, 2, 0, by decide, ?_⟩
  simp only [Finset.orderEmbOfFin_apply, four_sort, Fin.getElem_fin]
  decide +kernel

example : MakerWinsWithin ({0, 2, 3, 4} : Finset ℕ) 4 ∅ ∅ := by
  apply (makerWinsWithin_four_iff_isSymmetric _ (by decide)).2
  rw [show ({0, 2, 3, 4} : Finset ℕ).image (fun s : ℕ ↦ (s : ℚ)) = reflected by decide +kernel]
  refine ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, 1 / 2, 2, by norm_num, ?_⟩
  simp only [Finset.orderEmbOfFin_apply, reflected_sort, Fin.getElem_fin]
  decide +kernel

private def arithmetic : Finset ℚ := ([0, 1, 2, 3] : List ℚ).toFinset

private theorem arithmetic_sort : arithmetic.sort = [0, 1, 2, 3] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- Figure 4 at k = 1: four consecutive integers.
example : MakerWinsWithin ({0, 1, 2, 3} : Finset ℕ) 4 ∅ ∅ := by
  apply (makerWinsWithin_four_iff_isSymmetric _ (by decide)).2
  rw [show ({0, 1, 2, 3} : Finset ℕ).image (fun s : ℕ ↦ (s : ℚ)) = arithmetic by decide +kernel]
  refine ⟨⟨0, by decide⟩, ⟨3, by decide⟩, by decide, 1, 1, by decide, ?_⟩
  simp only [Finset.orderEmbOfFin_apply, arithmetic_sort, Fin.getElem_fin]
  decide +kernel

private def decreasingGaps : Finset ℚ := ([0, 4, 6, 7] : List ℚ).toFinset

private theorem decreasingGaps_sort : decreasingGaps.sort = [0, 4, 6, 7] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- Figure 4 also works without reversing a set whose gap ratio is k = 1/2.
example : MakerWinsWithin ({0, 4, 6, 7} : Finset ℕ) 4 ∅ ∅ := by
  apply (makerWinsWithin_four_iff_isSymmetric _ (by decide)).2
  have he : ({0, 4, 6, 7} : Finset ℕ).image (fun s : ℕ ↦ (s : ℚ)) = decreasingGaps := by
    decide +kernel
  rw [he]
  refine ⟨⟨0, by decide⟩, ⟨3, by decide⟩, by decide, 1 / 2, 4, by norm_num, ?_⟩
  simp only [Finset.orderEmbOfFin_apply, decreasingGaps_sort, Fin.getElem_fin]
  decide +kernel

private theorem triple_gap_ratio {p q r x y z : ℚ} (hpq : p < q) (hqr : q < r) (hxy : x < y)
    (hyz : y < z) (h : IsRatCopy {p, q, r} {x, y, z}) :
    (z - y) * (q - p) = (y - x) * (r - q) := by
  obtain ⟨a, b, ha, he⟩ := h
  simp only [Finset.image_insert, Finset.image_singleton] at he
  have hpq' : a * p + b < a * q + b := (add_lt_add_iff_right b).mpr (mul_lt_mul_of_pos_left hpq ha)
  have hqr' : a * q + b < a * r + b := (add_lt_add_iff_right b).mpr (mul_lt_mul_of_pos_left hqr ha)
  have hm (t : ℚ) : (t = a * p + b ∨ t = a * q + b ∨ t = a * r + b) ↔
      (t = x ∨ t = y ∨ t = z) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (show (t ∈ ({a * p + b, a * q + b, a * r + b} : Finset ℚ)) ↔
        t ∈ ({x, y, z} : Finset ℚ) by rw [he])
  have h₁ : a * p + b = x := by
    have hu := (hm (a * p + b)).mp (Or.inl rfl)
    have hv := (hm x).mpr (Or.inl rfl)
    rcases hu with h₁ | h₁ | h₁
    · exact h₁
    all_goals (rcases hv with h₂ | h₂ | h₂ <;> linarith only [h₁, h₂, hpq', hqr', hxy, hyz])
  have h₃ : a * r + b = z := by
    have hu := (hm (a * r + b)).mp (Or.inr (Or.inr rfl))
    have hv := (hm z).mpr (Or.inr (Or.inr rfl))
    rcases hu with h₃ | h₃ | h₃
    · rcases hv with h₂ | h₂ | h₂ <;> linarith only [h₃, h₂, hpq', hqr', hxy, hyz]
    · rcases hv with h₂ | h₂ | h₂ <;> linarith only [h₃, h₂, hpq', hqr', hxy, hyz]
    · exact h₃
  have h₂ : a * q + b = y := by
    rcases (hm (a * q + b)).mp (Or.inr (Or.inl rfl)) with h₂ | h₂ | h₂
    · linarith only [h₁, h₂, hpq']
    · exact h₂
    · linarith only [h₂, h₃, hqr']
  have hg₁ : y - x = a * (q - p) := by linear_combination h₁ - h₂
  have hg₂ : z - y = a * (r - q) := by linear_combination h₂ - h₃
  linear_combination (q - p) * hg₂ - (r - q) * hg₁

private def obstruction : Finset ℚ := ([0, 1, 3, 4] : List ℚ).toFinset

private theorem obstruction_sort : obstruction.sort = [0, 1, 3, 4] :=
  (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

-- The only possible symmetry types would equate distinct consecutive-gap ratios.
example : ¬ MakerWinsWithin ({0, 1, 3, 4} : Finset ℕ) 4 ∅ ∅ := by
  intro hw
  have hs := (makerWinsWithin_four_iff_isSymmetric _ (by decide)).mp hw
  have he : ({0, 1, 3, 4} : Finset ℕ).image (fun s : ℕ ↦ (s : ℚ)) = obstruction := by
    decide +kernel
  rw [he] at hs
  obtain ⟨i, j, hij⟩ := hs
  have hc := isSymmetricOfType_cases obstruction (by decide) i j hij
  change (i.val = 0 ∧ j.val = 3) ∨ (i.val = 1 ∧ j.val = 3) ∨ (i.val = 0 ∧ j.val = 2) at hc
  have noCopy {p q r x y z : ℚ} (hpq : p < q) (hqr : q < r) (hxy : x < y) (hyz : y < z)
      (hne : (z - y) * (q - p) ≠ (y - x) * (r - q)) : ¬ IsRatCopy {p, q, r} {x, y, z} :=
    fun h ↦ hne (triple_gap_ratio hpq hqr hxy hyz h)
  have h₀ : obstruction.erase (obstruction.orderEmbOfFin rfl ⟨0, by decide⟩) = {1, 3, 4} := by
    simp only [Finset.orderEmbOfFin_apply, obstruction_sort, Fin.getElem_fin]
    decide +kernel
  have h₁ : obstruction.erase (obstruction.orderEmbOfFin rfl ⟨1, by decide⟩) = {0, 3, 4} := by
    simp only [Finset.orderEmbOfFin_apply, obstruction_sort, Fin.getElem_fin]
    decide +kernel
  have h₂ : obstruction.erase (obstruction.orderEmbOfFin rfl ⟨2, by decide⟩) = {0, 1, 4} := by
    simp only [Finset.orderEmbOfFin_apply, obstruction_sort, Fin.getElem_fin]
    decide +kernel
  have h₃ : obstruction.erase (obstruction.orderEmbOfFin rfl ⟨3, by decide⟩) = {0, 1, 3} := by
    simp only [Finset.orderEmbOfFin_apply, obstruction_sort, Fin.getElem_fin]
    decide +kernel
  rcases hc with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hi' : i = ⟨0, by decide⟩ := Fin.ext hi
    have hj' : j = ⟨3, by decide⟩ := Fin.ext hj
    subst i j
    exact noCopy (p := 0) (q := 1) (r := 3) (x := 1) (y := 3) (z := 4)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (h₃ ▸ h₀ ▸ hij.2)
  · have hi' : i = ⟨1, by decide⟩ := Fin.ext hi
    have hj' : j = ⟨3, by decide⟩ := Fin.ext hj
    subst i j
    exact noCopy (p := 0) (q := 1) (r := 3) (x := 0) (y := 3) (z := 4)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (h₃ ▸ h₁ ▸ hij.2)
  · have hi' : i = ⟨0, by decide⟩ := Fin.ext hi
    have hj' : j = ⟨2, by decide⟩ := Fin.ext hj
    subst i j
    exact noCopy (p := 0) (q := 1) (r := 4) (x := 1) (y := 3) (z := 4)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (h₂ ▸ h₀ ▸ hij.2)
