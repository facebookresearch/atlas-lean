/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive differences in the Kumar–Mohan–Pandey sets
-/

namespace MetaMathlibExt

open scoped Pointwise

private theorem partial_append (a : ℤ) (p q : List ℕ) :
    setOfConsecutiveDifferences a (p ++ q) =
      setOfConsecutiveDifferences a p ∪ setOfConsecutiveDifferences (a + (p.sum : ℤ)) q := by
  induction p generalizing a with
  | nil =>
      have ha : a ∈ setOfConsecutiveDifferences a q := by
        cases q <;> simp [setOfConsecutiveDifferences]
      simp [setOfConsecutiveDifferences, ha]
  | cons g p ih =>
      simp [setOfConsecutiveDifferences_cons, ih, Finset.insert_union, add_assoc]

private theorem block_sum (k : ℕ) : (chuBlock k).sum = 4 * (k + 1) := by
  simp [chuBlock, List.sum_append]
  omega

private theorem fours (n : ℕ) (a x : ℤ)
    (hx : x ∈ setOfConsecutiveDifferences a (List.replicate n 4)) :
    ∃ i : ℤ, x = a + 4 * i := by
  induction n generalizing a with
  | zero => simp [setOfConsecutiveDifferences] at hx; exact ⟨0, by omega⟩
  | succ n ih =>
      simp only [List.replicate_succ, setOfConsecutiveDifferences_cons,
        Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨0, by omega⟩
      · obtain ⟨i, hi⟩ := ih (a + 4) hx
        exact ⟨i + 1, by omega⟩

private theorem block_shape (k : ℕ) (a x : ℤ)
    (hx : x ∈ setOfConsecutiveDifferences a (chuBlock k)) :
    x = a ∨ x = a + 4 * (k + 1 : ℕ) ∨ ∃ i : ℤ, x = a + 4 * i + 1 := by
  change x ∈ setOfConsecutiveDifferences a (1 :: (List.replicate k 4 ++ [3])) at hx
  rw [setOfConsecutiveDifferences_cons, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · rw [partial_append] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi⟩ := fours k (a + 1) x hx
      exact Or.inr (Or.inr ⟨i, by omega⟩)
    · simp only [setOfConsecutiveDifferences, Finset.mem_insert,
        Finset.mem_singleton, List.sum_replicate, nsmul_eq_mul, Int.natCast_mul] at hx
      norm_num at hx
      rcases hx with hx | hx
      · exact Or.inr (Or.inr ⟨k, by omega⟩)
      · exact Or.inr (Or.inl (by omega))

private theorem inner_shape (k l : ℕ) (a x : ℤ)
    (hx : x ∈ setOfConsecutiveDifferences a (List.replicate l (chuBlock k)).flatten) :
    (∃ i : ℤ, 0 ≤ i ∧ i ≤ l ∧ x = a + 4 * (k + 1 : ℕ) * i) ∨
      ∃ i : ℤ, x = a + 4 * i + 1 := by
  induction l generalizing a with
  | zero =>
      simp [setOfConsecutiveDifferences] at hx
      exact Or.inl ⟨0, by omega, by omega, by omega⟩
  | succ l ih =>
      rw [List.replicate_succ, List.flatten_cons, partial_append] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases block_shape k a x hx with hx | hx | hx
        · exact Or.inl ⟨0, by omega, by omega, by omega⟩
        · exact Or.inl ⟨1, by omega, by omega, by omega⟩
        · exact Or.inr hx
      · rcases ih (a + ((chuBlock k).sum : ℤ)) hx with ⟨i, hi, hil, hx⟩ | ⟨i, hx⟩
        · refine Or.inl ⟨i + 1, by omega, by omega, ?_⟩
          simp only [block_sum, Int.natCast_mul] at hx
          linear_combination hx
        · refine Or.inr ⟨(k + 1 : ℕ) + i, ?_⟩
          simp only [block_sum, Int.natCast_mul] at hx
          linear_combination hx

private def outerBlock (k l : ℕ) : List ℕ :=
  [1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten

private theorem outer_sum (k l : ℕ) :
    (outerBlock k l).sum = 4 * (l * (k + 1) + 1) := by
  simp [outerBlock, List.sum_flatten, block_sum]
  ring

private theorem outer_shape (k l : ℕ) (a x : ℤ)
    (hx : x ∈ setOfConsecutiveDifferences a (outerBlock k l)) :
    x = a ∨ x = a + 2 ∨
      (∃ i : ℤ, 0 ≤ i ∧ i ≤ l ∧ x = a + 4 + 4 * (k + 1 : ℕ) * i) ∨
      ∃ i : ℤ, x = a + 4 * i + 1 := by
  rw [outerBlock, partial_append] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · simp only [setOfConsecutiveDifferences, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr ⟨0, by omega⟩))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl ⟨0, by omega, by omega, by norm_num at hx ⊢; omega⟩))
  · norm_num at hx
    rcases inner_shape k l (a + 4) x hx with hx | ⟨i, hx⟩
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr ⟨i + 1, by omega⟩))

private theorem repeated_shape (k l t : ℕ) (a x : ℤ)
    (hx : x ∈ setOfConsecutiveDifferences a (List.replicate t (outerBlock k l)).flatten) :
    (∃ j : ℤ, 0 ≤ j ∧ j ≤ t ∧ x = a + 4 * (l * (k + 1) + 1 : ℕ) * j) ∨
    (∃ j : ℤ, 0 ≤ j ∧ j < t ∧ x = a + 4 * (l * (k + 1) + 1 : ℕ) * j + 2) ∨
    (∃ j i : ℤ, 0 ≤ j ∧ j < t ∧ 0 ≤ i ∧ i ≤ l ∧
      x = a + 4 * (l * (k + 1) + 1 : ℕ) * j + 4 + 4 * (k + 1 : ℕ) * i) ∨
    ∃ i : ℤ, x = a + 4 * i + 1 := by
  induction t generalizing a with
  | zero =>
      simp [setOfConsecutiveDifferences] at hx
      exact Or.inl ⟨0, by omega, by omega, by omega⟩
  | succ t ih =>
      rw [List.replicate_succ, List.flatten_cons, partial_append] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases outer_shape k l a x hx with hx | hx | ⟨i, hi, hil, hx⟩ | hx
        · exact Or.inl ⟨0, by omega, by omega, by omega⟩
        · exact Or.inr (Or.inl ⟨0, by omega, by omega, by omega⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨0, i, by omega, by omega, hi, hil, by omega⟩))
        · exact Or.inr (Or.inr (Or.inr hx))
      · rcases ih (a + ((outerBlock k l).sum : ℤ)) hx with
          ⟨j, hj, hjt, hx⟩ | ⟨j, hj, hjt, hx⟩ | ⟨j, i, hj, hjt, hi, hil, hx⟩ | ⟨i, hx⟩
        · refine Or.inl ⟨j + 1, by omega, by omega, ?_⟩
          simp only [outer_sum, Int.natCast_mul] at hx
          linear_combination hx
        · refine Or.inr (Or.inl ⟨j + 1, by omega, by omega, ?_⟩)
          simp only [outer_sum, Int.natCast_mul] at hx
          linear_combination hx
        · refine Or.inr (Or.inr (Or.inl ⟨j + 1, i, by omega, by omega, hi, hil, ?_⟩))
          simp only [outer_sum, Int.natCast_mul] at hx
          linear_combination hx
        · refine Or.inr (Or.inr (Or.inr ⟨(l * (k + 1) + 1 : ℕ) + i, ?_⟩))
          simp only [outer_sum, Int.natCast_mul] at hx
          linear_combination hx

private theorem family_shape (k l t : ℕ) (x : ℤ) (hx : x ∈ chuFamilyKLT k l t) :
    x = 0 ∨ x = 4 * (l * (k + 1) + 1 : ℕ) * t + 4 ∨
    (∃ j i : ℤ, 0 ≤ j ∧ j < t ∧ 0 ≤ i ∧ i ≤ l ∧
      x = 4 * (l * (k + 1) + 1 : ℕ) * j + 4 + 4 * (k + 1 : ℕ) * i) ∨
    (∃ j : ℤ, 0 ≤ j ∧ j ≤ t ∧ x = 4 * (l * (k + 1) + 1 : ℕ) * j + 2) ∨
    ∃ i : ℤ, x = 4 * i + 1 := by
  change x ∈ setOfConsecutiveDifferences 0
    ((List.replicate t (outerBlock k l)).flatten ++ [1, 1, 2, 1]) at hx
  rw [partial_append] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases repeated_shape k l t 0 x hx with
        ⟨j, hj, hjt, hx⟩ | ⟨j, hj, hjt, hx⟩ | ⟨j, i, hj, hjt, hi, hil, hx⟩ | ⟨i, hx⟩
    · by_cases h : j = 0
      · exact Or.inl (by simpa only [h, mul_zero, zero_add] using hx)
      · refine Or.inr (Or.inr (Or.inl ⟨j - 1, l, by omega, by omega,
          by positivity, le_rfl, ?_⟩))
        simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] at hx ⊢
        linear_combination hx
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨j, i, hj, hjt, hi, hil, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega⟩)))
  · have hs : (List.replicate t (outerBlock k l)).flatten.sum =
        t * (4 * (l * (k + 1) + 1)) := by simp [List.sum_flatten, outer_sum]
    simp only [hs, Int.natCast_mul, zero_add, setOfConsecutiveDifferences,
      Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx | hx
    · by_cases h : t = 0
      · exact Or.inl (by simpa only [h, Nat.cast_zero, zero_mul] using hx)
      · refine Or.inr (Or.inr (Or.inl ⟨(t : ℤ) - 1, l, by omega, by omega,
          by positivity, le_rfl, ?_⟩))
        simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] at hx ⊢
        linear_combination hx
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(l * (k + 1) + 1 : ℕ) * t, by push_cast at hx ⊢; linear_combination hx⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨t, by positivity, le_rfl, by push_cast at hx ⊢; linear_combination hx⟩)))
    · exact Or.inr (Or.inl (by push_cast at hx ⊢; linear_combination hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(l * (k + 1) + 1 : ℕ) * t + 1, by push_cast at hx ⊢; linear_combination hx⟩)))

private theorem mem_repeat (b : List ℕ) (n j : ℕ) (a x : ℤ) (hj : j < n)
    (hx : x ∈ setOfConsecutiveDifferences (a + (b.sum : ℤ) * j) b) :
    x ∈ setOfConsecutiveDifferences a (List.replicate n b).flatten := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, partial_append, Finset.mem_union]
      cases j with
      | zero => left; simpa using hx
      | succ j =>
          right
          apply ih j (a + (b.sum : ℤ)) (by omega)
          have he : a + (b.sum : ℤ) * (j + 1 : ℕ) =
              a + (b.sum : ℤ) + (b.sum : ℤ) * j := by push_cast; ring
          simpa only [he] using hx

private theorem mem_two (k l t j : ℕ) (hj : j ≤ t) :
    4 * (l * (k + 1) + 1 : ℤ) * (j : ℤ) + 2 ∈ chuFamilyKLT k l t := by
  change _ ∈ setOfConsecutiveDifferences 0
    ((List.replicate t (outerBlock k l)).flatten ++ [1, 1, 2, 1])
  rw [partial_append, Finset.mem_union]
  by_cases h : j < t
  · left
    apply mem_repeat (outerBlock k l) t j 0 _ h
    simp only [outer_sum, Int.natCast_mul, zero_add]
    simp [outerBlock, setOfConsecutiveDifferences]
    omega
  · right
    have he : j = t := by omega
    subst j
    simp [List.sum_flatten, outer_sum, setOfConsecutiveDifferences, mul_comm]
    omega

private def firstDifferences (k l t : ℕ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) t).image fun n => 4 * (l * (k + 1) + 1 : ℕ) * n + 2

private def secondDifferences (k l t : ℕ) : Finset ℤ :=
  (Finset.Icc (0 : ℤ) ((t : ℤ) - 1) ×ˢ Finset.Icc (1 : ℤ) l).image fun p =>
    4 * (l * (k + 1) + 1 : ℕ) * p.1 + 4 * (k + 1 : ℕ) * p.2 + 2

private theorem difference_indices (q B L T n i : ℤ)
    (hq : 0 < q) (hL : 0 ≤ L) (hB : B = q * L + 1)
    (hi : 0 ≤ i) (hil : i ≤ L) (hnt : n < T)
    (hd : 6 ≤ 4 * B * n + 4 * q * i + 2) :
    (i = 0 ∧ 1 ≤ n ∧ n ≤ T) ∨ (1 ≤ i ∧ 0 ≤ n ∧ n ≤ T - 1) := by
  have hBpos : 0 < B := by nlinarith
  have hoff : 0 ≤ q * i ∧ q * i < B := by constructor <;> nlinarith
  have hn : 0 ≤ n := by
    by_contra h
    have : n ≤ -1 := by omega
    nlinarith
  by_cases h : i = 0
  · left
    refine ⟨h, ?_, by omega⟩
    subst i
    by_contra h
    have : n = 0 := by omega
    simp [this] at hd
  · exact Or.inr ⟨by omega, hn, by omega⟩

private def zeroIndices (q B L T u : ℤ) : Prop :=
  u = 0 ∨ u = B * T + 1 ∨
    ∃ j i : ℤ, 0 ≤ j ∧ j < T ∧ 0 ≤ i ∧ i ≤ L ∧ u = B * j + 1 + q * i

private theorem family_residues (k l t : ℕ) (x : ℤ) (hx : x ∈ chuFamilyKLT k l t) :
    x % 4 = 1 ∨
    (∃ u : ℤ, x = 4 * u ∧ zeroIndices (k + 1) (l * (k + 1) + 1) l t u) ∨
    ∃ j : ℤ, 0 ≤ j ∧ j ≤ t ∧ x = 4 * ((l * (k + 1) + 1 : ℤ) * j) + 2 := by
  rcases family_shape k l t x hx with hx | hx | ⟨j, i, hj, hjt, hi, hil, hx⟩ |
      ⟨j, hj, hjt, hx⟩ | ⟨i, hx⟩
  · exact Or.inr (Or.inl ⟨0, by omega, Or.inl rfl⟩)
  · refine Or.inr (Or.inl ⟨(l * (k + 1) + 1 : ℤ) * t + 1, ?_, Or.inr (Or.inl rfl)⟩)
    push_cast at hx
    linear_combination hx
  · refine Or.inr (Or.inl ⟨(l * (k + 1) + 1 : ℤ) * j + 1 + (k + 1 : ℤ) * i,
        ?_, Or.inr (Or.inr ⟨j, i, hj, hjt, hi, hil, rfl⟩)⟩)
    push_cast at hx
    linear_combination hx
  · refine Or.inr (Or.inr ⟨j, hj, hjt, ?_⟩)
    push_cast at hx
    linear_combination hx
  · left
    omega

private theorem indexed_mem (k l t : ℕ) (n i : ℤ) (hi : 0 ≤ i) (hil : i ≤ l)
    (hnt : n < t)
    (hd : 6 ≤ 4 * (l * (k + 1) + 1 : ℤ) * n + 4 * (k + 1 : ℤ) * i + 2) :
    4 * (l * (k + 1) + 1 : ℤ) * n + 4 * (k + 1 : ℤ) * i + 2 ∈
      firstDifferences k l t ∪ secondDifferences k l t := by
  rcases difference_indices (k + 1) (l * (k + 1) + 1) l t n i
      (by positivity) (by positivity) (by ring) hi hil hnt hd with
      ⟨rfl, hn, hnt⟩ | ⟨hi, hn, hnt⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨n, Finset.mem_Icc.mpr ⟨hn, hnt⟩, by simp⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(n, i), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hn, hnt⟩, Finset.mem_Icc.mpr ⟨hi, hil⟩⟩, by rfl⟩

private theorem positive_zero_two (k l t : ℕ) (u j : ℤ)
    (hu : zeroIndices (k + 1) (l * (k + 1) + 1) l t u)
    (hj : 0 ≤ j) (hjt : j ≤ t)
    (hd : 6 ≤ 4 * u - (4 * ((l * (k + 1) + 1 : ℤ) * j) + 2)) :
    4 * u - (4 * ((l * (k + 1) + 1 : ℤ) * j) + 2) ∈
      firstDifferences k l t ∪ secondDifferences k l t := by
  let q : ℤ := k + 1
  let B : ℤ := l * (k + 1) + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  change zeroIndices q B l t u at hu
  change 6 ≤ 4 * u - (4 * (B * j) + 2) at hd
  rcases hu with rfl | rfl | ⟨a, i, ha, hat, hi, hil, rfl⟩
  · have : 0 ≤ B * j := mul_nonneg (le_of_lt hB) hj
    omega
  · have hn : 1 ≤ (t : ℤ) - j := by
      by_contra h
      have : (t : ℤ) = j := by omega
      simp [this] at hd
      omega
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨(t : ℤ) - j, Finset.mem_Icc.mpr ⟨hn, by omega⟩, by
      change 4 * B * ((t : ℤ) - j) + 2 = _
      ring⟩
  · have he : 4 * (B * a + 1 + q * i) - (4 * (B * j) + 2) =
        4 * B * (a - j) + 4 * q * i + 2 := by ring
    rw [he] at hd ⊢
    exact indexed_mem k l t (a - j) i hi hil (by omega) hd

private theorem positive_two_zero (k l t : ℕ) (u j : ℤ)
    (hu : zeroIndices (k + 1) (l * (k + 1) + 1) l t u)
    (hj : 0 ≤ j) (hjt : j ≤ t)
    (hd : 6 ≤ (4 * ((l * (k + 1) + 1 : ℤ) * j) + 2) - 4 * u) :
    (4 * ((l * (k + 1) + 1 : ℤ) * j) + 2) - 4 * u ∈
      firstDifferences k l t ∪ secondDifferences k l t := by
  let q : ℤ := k + 1
  let B : ℤ := l * (k + 1) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  change zeroIndices q B l t u at hu
  change 6 ≤ (4 * (B * j) + 2) - 4 * u at hd
  rcases hu with rfl | rfl | ⟨a, i, ha, hat, hi, hil, rfl⟩
  · have hn : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at hd
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_Icc.mpr ⟨hn, hjt⟩, by change 4 * B * j + 2 = _; ring⟩
  · have : B * j ≤ B * t := mul_le_mul_of_nonneg_left hjt (le_of_lt hB)
    omega
  · have he : (4 * (B * j) + 2) - 4 * (B * a + 1 + q * i) =
        4 * B * (j - a - 1) + 4 * q * ((l : ℤ) - i) + 2 := by dsimp [B, q]; ring
    rw [he] at hd ⊢
    exact indexed_mem k l t (j - a - 1) ((l : ℤ) - i) (by omega) (by omega)
      (by omega) hd

private theorem filtered_subset (k l t : ℕ) :
    (chuFamilyKLT k l t - chuFamilyKLT k l t).filter (fun d => 6 ≤ d ∧ d % 4 = 2) ⊆
      firstDifferences k l t ∪ secondDifferences k l t := by
  intro d hd
  obtain ⟨hd, hpos, hmod⟩ := Finset.mem_filter.mp hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
  rcases family_residues k l t a ha with ha | ⟨u, rfl, hu⟩ | ⟨j, hj, hjt, rfl⟩
  · rcases family_residues k l t b hb with hb | ⟨v, rfl, _⟩ | ⟨j, _, _, rfl⟩ <;> omega
  · rcases family_residues k l t b hb with hb | ⟨v, rfl, _⟩ | ⟨j, hj, hjt, rfl⟩
    · omega
    · omega
    · exact positive_zero_two k l t u j hu hj hjt hpos
  · rcases family_residues k l t b hb with hb | ⟨u, rfl, hu⟩ | ⟨a, _, _, rfl⟩
    · omega
    · exact positive_two_zero k l t u j hu hj hjt hpos
    · omega

private theorem differences_subset {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    firstDifferences k l t ∪ secondDifferences k l t ⊆
      (chuFamilyKLT k l t - chuFamilyKLT k l t).filter (fun d => 6 ≤ d ∧ d % 4 = 2) := by
  have hzero : (0 : ℤ) ∈ chuFamilyKLT k l t := by
    unfold chuFamilyKLT
    cases ((List.replicate t ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten)).flatten ++
      [1, 1, 2, 1]) <;> simp [setOfConsecutiveDifferences]
  have htwo : (2 : ℤ) ∈ chuFamilyKLT k l t := by simpa using mem_two k l t 0 (by omega)
  let q : ℤ := k + 1
  let B : ℤ := l * (k + 1) + 1
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hB : 1 ≤ B := by
    have : 0 ≤ (l : ℤ) * (k + 1) := by positivity
    dsimp [B]
    omega
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hn, hnt⟩ := Finset.mem_Icc.mp hn
    have hmem := mem_two k l t n.toNat (by omega)
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    rw [hncast] at hmem
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa using Finset.sub_mem_sub hmem hzero
    · change 6 ≤ 4 * B * n + 2
      nlinarith
    · change (4 * B * n + 2) % 4 = 2
      have he : 4 * B * n + 2 = 4 * (B * n) + 2 := by ring
      rw [he]
      omega
  · obtain ⟨⟨n, i⟩, hni, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hn, hi⟩ := Finset.mem_product.mp hni
    obtain ⟨hn, hnt⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hi, hil⟩ := Finset.mem_Icc.mp hi
    have hstart := chuFamilyKLT_mem_block_starts hk hl ht i.toNat n.toNat
      (by omega) (by omega)
    have hicast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    rw [hicast, hncast] at hstart
    have he : 4 + (4 * (k : ℤ) + 4) * i +
        (4 * k * l + 4 * l + 4) * n - 2 = 4 * B * n + 4 * q * i + 2 := by
      dsimp [B, q]
      ring
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · convert Finset.sub_mem_sub hstart htwo using 1
      exact he.symm
    · change 6 ≤ 4 * B * n + 4 * q * i + 2
      have : 0 ≤ B * n := mul_nonneg (by omega) hn
      nlinarith
    · change (4 * B * n + 4 * q * i + 2) % 4 = 2
      have he : 4 * B * n + 4 * q * i + 2 = 4 * (B * n + q * i) + 2 := by ring
      rw [he]
      omega

private theorem indices_unique (q B L n i m j : ℤ) (hq : 0 < q)
    (hB : B = q * L + 1) (hi : 0 ≤ i) (hil : i ≤ L) (hj : 0 ≤ j) (hjl : j ≤ L)
    (h : B * n + q * i = B * m + q * j) : n = m ∧ i = j := by
  have hL : 0 ≤ L := by omega
  have hBpos : 0 < B := by nlinarith
  have hio : 0 ≤ q * i ∧ q * i < B := by constructor <;> nlinarith
  have hjo : 0 ≤ q * j ∧ q * j < B := by constructor <;> nlinarith
  have hnm : n = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : n + 1 ≤ m := by omega
      nlinarith
    · have : m + 1 ≤ n := by omega
      nlinarith
  refine ⟨hnm, ?_⟩
  rw [hnm] at h
  nlinarith

private theorem differences_card (k l t : ℕ) :
    (firstDifferences k l t ∪ secondDifferences k l t).card = l * t + t := by
  let q : ℤ := k + 1
  let B : ℤ := l * (k + 1) + 1
  have hq : 0 < q := by dsimp [q]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hB : B = q * l + 1 := by dsimp [B, q]; ring
  have hfirst : (firstDifferences k l t).card = t := by
    rw [firstDifferences, Finset.card_image_of_injective]
    · simp
    · intro n m h
      change 4 * B * n + 2 = 4 * B * m + 2 at h
      nlinarith
  have hsecond : (secondDifferences k l t).card = t * l := by
    rw [secondDifferences, Finset.card_image_of_injOn]
    · simp [Finset.card_product]
    · intro p hp r hr h
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
      obtain ⟨hr₁, hr₂⟩ := Finset.mem_product.mp hr
      obtain ⟨hi, hil⟩ := Finset.mem_Icc.mp hp₂
      obtain ⟨hj, hjl⟩ := Finset.mem_Icc.mp hr₂
      change 4 * B * p.1 + 4 * q * p.2 + 2 = 4 * B * r.1 + 4 * q * r.2 + 2 at h
      obtain ⟨hn, hi⟩ := indices_unique q B l p.1 p.2 r.1 r.2 hq hB
        (by omega) hil (by omega) hjl (by linarith)
      exact Prod.ext hn hi
  have hdisjoint : Disjoint (firstDifferences k l t) (secondDifferences k l t) := by
    apply Finset.disjoint_left.mpr
    intro d hd₁ hd₂
    obtain ⟨n, _, h₁⟩ := Finset.mem_image.mp hd₁
    obtain ⟨⟨m, i⟩, hmi, h₂⟩ := Finset.mem_image.mp hd₂
    obtain ⟨_, hi⟩ := Finset.mem_product.mp hmi
    obtain ⟨hi, hil⟩ := Finset.mem_Icc.mp hi
    change 4 * B * n + 2 = d at h₁
    change 4 * B * m + 4 * q * i + 2 = d at h₂
    obtain ⟨_, he⟩ := indices_unique q B l n 0 m i hq hB (by omega) (by positivity)
      (by omega) hil (by linarith)
    omega
  rw [Finset.card_union_of_disjoint hdisjoint, hfirst, hsecond]
  simp [Nat.mul_comm, Nat.add_comm]

/-- **Positive differences of the form 6 + 4m in the Chu family set.** Let $k$, $l$, $t$ be
positive integers and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$,
$t$. Then exactly $lt + t$ elements $d$ of $A - A$ satisfy $d \ge 6$ and $d \equiv 2 \pmod 4$;
that is, exactly $lt + t$ positive differences of $A$ have the form $6 + 4m$ with $m \ge 0$ an
integer.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 3 (`integers-2024-A32-lem-3`). -/
public theorem chuFamilyKLT_card_sub_six_add_four_mul {k l t : ℕ} (hk : 0 < k)
    (hl : 0 < l) (ht : 0 < t) :
    ((chuFamilyKLT k l t - chuFamilyKLT k l t).filter
        fun d => 6 ≤ d ∧ d % 4 = 2).card = l * t + t := by
  rw [Finset.Subset.antisymm (filtered_subset k l t) (differences_subset hk hl ht)]
  exact differences_card k l t

end MetaMathlibExt
