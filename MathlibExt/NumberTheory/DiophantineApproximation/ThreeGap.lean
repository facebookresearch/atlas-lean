/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The three-gap theorem

This file proves that the fractional parts of the first `n` multiples of an irrational real
number cut the circle into gaps of at most three distinct lengths. If three lengths occur, the
largest is the sum of the other two.
-/

@[expose] public section

namespace MetaMathlibExt

private noncomputable def threeGap_fract (α : ℝ) (m : ℤ) : ℝ :=
  Int.fract ((m : ℝ) * α)

private noncomputable def threeGap_natFract (α : ℝ) (k : ℕ) : ℝ :=
  threeGap_fract α (k : ℤ)

private noncomputable def threeGap_distance (α : ℝ) (k j : ℕ) : ℝ :=
  threeGap_fract α ((j : ℤ) - (k : ℤ))

private theorem threeGap_natFract_eq (α : ℝ) (k : ℕ) :
    threeGap_natFract α k = Int.fract ((k : ℝ) * α) := by
  simp [threeGap_natFract, threeGap_fract]

private theorem threeGap_fract_ne_zero (α : ℝ) (hα : Irrational α) {m : ℤ} (hm : m ≠ 0) :
    threeGap_fract α m ≠ 0 := by
  rw [threeGap_fract, Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  exact (hα.intCast_mul hm).ne_int z hz.symm

private theorem threeGap_fract_pos (α : ℝ) (hα : Irrational α) {m : ℤ} (hm : m ≠ 0) :
    0 < threeGap_fract α m := by
  exact lt_of_le_of_ne (Int.fract_nonneg _) (threeGap_fract_ne_zero α hα hm).symm

private theorem threeGap_fract_neg (α : ℝ) (hα : Irrational α) {m : ℤ} (hm : m ≠ 0) :
    threeGap_fract α (-m) = 1 - threeGap_fract α m := by
  rw [threeGap_fract, show ((-m : ℤ) : ℝ) * α = -((m : ℝ) * α) by push_cast; ring]
  exact Int.fract_neg (threeGap_fract_ne_zero α hα hm)

private theorem threeGap_fract_add_of_lt_one (α : ℝ) (a b : ℤ)
    (h : threeGap_fract α a + threeGap_fract α b < 1) :
    threeGap_fract α (a + b) = threeGap_fract α a + threeGap_fract α b := by
  calc
    threeGap_fract α (a + b) =
        Int.fract (((a : ℝ) * α) + ((b : ℝ) * α)) := by
      unfold threeGap_fract
      congr 2
      push_cast
      ring
    _ = Int.fract (threeGap_fract α a + threeGap_fract α b) := by
      symm
      exact Int.fract_fract_add_fract _ _
    _ = threeGap_fract α a + threeGap_fract α b := by
      rw [Int.fract_eq_self]
      exact ⟨add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _), h⟩

private theorem threeGap_fract_add_of_one_le (α : ℝ) (a b : ℤ)
    (h : 1 ≤ threeGap_fract α a + threeGap_fract α b) :
    threeGap_fract α (a + b) = threeGap_fract α a + threeGap_fract α b - 1 := by
  have ha : threeGap_fract α a < 1 := Int.fract_lt_one _
  have hb : threeGap_fract α b < 1 := Int.fract_lt_one _
  calc
    threeGap_fract α (a + b) =
        Int.fract (((a : ℝ) * α) + ((b : ℝ) * α)) := by
      unfold threeGap_fract
      congr 2
      push_cast
      ring
    _ = Int.fract (threeGap_fract α a + threeGap_fract α b) := by
      symm
      exact Int.fract_fract_add_fract _ _
    _ = Int.fract (threeGap_fract α a + threeGap_fract α b - 1) := by
      symm
      exact Int.fract_sub_one _
    _ = threeGap_fract α a + threeGap_fract α b - 1 := by
      rw [Int.fract_eq_self]
      constructor <;> linarith

private theorem threeGap_fract_sub_of_le (α : ℝ) (a b : ℤ)
    (h : threeGap_fract α b ≤ threeGap_fract α a) :
    threeGap_fract α (a - b) = threeGap_fract α a - threeGap_fract α b := by
  have ha : threeGap_fract α a < 1 := Int.fract_lt_one _
  have hb : 0 ≤ threeGap_fract α b := Int.fract_nonneg _
  calc
    threeGap_fract α (a - b) =
        Int.fract (((a : ℝ) * α) - ((b : ℝ) * α)) := by
      unfold threeGap_fract
      congr 2
      push_cast
      ring
    _ = Int.fract (threeGap_fract α a - threeGap_fract α b) := by
      symm
      exact Int.fract_fract_sub_fract _ _
    _ = threeGap_fract α a - threeGap_fract α b := by
      rw [Int.fract_eq_self]
      constructor <;> linarith

private theorem threeGap_fract_sub_of_lt (α : ℝ) (a b : ℤ)
    (h : threeGap_fract α a < threeGap_fract α b) :
    threeGap_fract α (a - b) = 1 + threeGap_fract α a - threeGap_fract α b := by
  have ha : 0 ≤ threeGap_fract α a := Int.fract_nonneg _
  have hb : threeGap_fract α b < 1 := Int.fract_lt_one _
  calc
    threeGap_fract α (a - b) =
        Int.fract (((a : ℝ) * α) - ((b : ℝ) * α)) := by
      unfold threeGap_fract
      congr 2
      push_cast
      ring
    _ = Int.fract (threeGap_fract α a - threeGap_fract α b) := by
      symm
      exact Int.fract_fract_sub_fract _ _
    _ = Int.fract (threeGap_fract α a - threeGap_fract α b + 1) := by
      symm
      exact Int.fract_add_one _
    _ = threeGap_fract α a - threeGap_fract α b + 1 := by
      rw [Int.fract_eq_self]
      constructor <;> linarith
    _ = 1 + threeGap_fract α a - threeGap_fract α b := by ring

private theorem threeGap_fract_injective (α : ℝ) (hα : Irrational α) :
    Function.Injective (threeGap_fract α) := by
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hnz := threeGap_fract_ne_zero α hα hsub
  rw [threeGap_fract_sub_of_le α a b hab.ge, hab, sub_self] at hnz
  exact hnz rfl

private theorem threeGap_natFract_injective (α : ℝ) (hα : Irrational α) :
    Function.Injective (threeGap_natFract α) := by
  intro a b hab
  have hi : (a : ℤ) = (b : ℤ) := threeGap_fract_injective α hα hab
  exact_mod_cast hi

private theorem threeGap_distance_of_le (α : ℝ) {k j : ℕ} (hkj : k ≤ j) :
    threeGap_distance α k j = threeGap_natFract α (j - k) := by
  unfold threeGap_distance threeGap_natFract
  rw [Int.ofNat_sub hkj]

private theorem threeGap_distance_of_lt (α : ℝ) (hα : Irrational α) {j k : ℕ}
    (hjk : j < k) :
    threeGap_distance α k j = 1 - threeGap_natFract α (k - j) := by
  have hsub : ((k - j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : k - j ≠ 0)
  have heq : (j : ℤ) - (k : ℤ) = -((k - j : ℕ) : ℤ) := by
    rw [Int.ofNat_sub hjk.le]
    omega
  unfold threeGap_distance threeGap_natFract
  rw [heq, threeGap_fract_neg α hα hsub]

private theorem threeGap_distance_eq_sub_of_value_le (α : ℝ) {k j : ℕ}
    (h : threeGap_natFract α k ≤ threeGap_natFract α j) :
    threeGap_distance α k j = threeGap_natFract α j - threeGap_natFract α k := by
  simpa [threeGap_distance, threeGap_natFract] using
    threeGap_fract_sub_of_le α (j : ℤ) (k : ℤ) h

private theorem threeGap_distance_eq_add_sub_of_value_lt (α : ℝ) {k j : ℕ}
    (h : threeGap_natFract α j < threeGap_natFract α k) :
    threeGap_distance α k j = 1 + threeGap_natFract α j - threeGap_natFract α k := by
  simpa [threeGap_distance, threeGap_natFract] using
    threeGap_fract_sub_of_lt α (j : ℤ) (k : ℤ) h

private theorem threeGap_exists_extrema (n : ℕ) (hn : 2 ≤ n) (α : ℝ) :
    ∃ u v : ℕ,
      1 ≤ u ∧ u < n ∧ 1 ≤ v ∧ v < n ∧
      (∀ m : ℕ, 1 ≤ m → m < n → threeGap_natFract α u ≤ threeGap_natFract α m) ∧
      (∀ m : ℕ, 1 ≤ m → m < n → threeGap_natFract α m ≤ threeGap_natFract α v) := by
  have hs : (Finset.Ico 1 n).Nonempty := Finset.nonempty_Ico.mpr (by omega)
  obtain ⟨u, hu, humin⟩ := Finset.exists_min_image (Finset.Ico 1 n)
    (threeGap_natFract α) hs
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image (Finset.Ico 1 n)
    (threeGap_natFract α) hs
  rw [Finset.mem_Ico] at hu hv
  exact ⟨u, v, hu.1, hu.2, hv.1, hv.2,
    fun m hm hmn => humin m (Finset.mem_Ico.mpr ⟨hm, hmn⟩),
    fun m hm hmn => hvmax m (Finset.mem_Ico.mpr ⟨hm, hmn⟩)⟩

private theorem threeGap_extrema_sum_ge (n u v : ℕ) (α : ℝ) (hα : Irrational α)
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v) :
    n ≤ u + v := by
  by_contra hsum
  have huv_lt : u + v < n := by omega
  have huv_pos : 1 ≤ u + v := by omega
  have hu0 : (u : ℤ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
  have hfu_pos : 0 < threeGap_natFract α u := threeGap_fract_pos α hα hu0
  have hfv_lt : threeGap_natFract α v < 1 := Int.fract_lt_one _
  by_cases hlt : threeGap_natFract α u + threeGap_natFract α v < 1
  · have hadd : threeGap_natFract α (u + v) =
        threeGap_natFract α u + threeGap_natFract α v := by
      simpa [threeGap_natFract] using
        threeGap_fract_add_of_lt_one α (u : ℤ) (v : ℤ) hlt
    have hmax := hvmax (u + v) huv_pos huv_lt
    rw [hadd] at hmax
    linarith
  · have hadd : threeGap_natFract α (u + v) =
        threeGap_natFract α u + threeGap_natFract α v - 1 := by
      simpa [threeGap_natFract] using
        threeGap_fract_add_of_one_le α (u : ℤ) (v : ℤ) (le_of_not_gt hlt)
    have hmin := humin (u + v) huv_pos huv_lt
    rw [hadd] at hmin
    linarith

private theorem threeGap_forward_lower (n u k : ℕ) (α : ℝ) (hα : Irrational α)
    (hu : 1 ≤ u) (hku : k + u < n)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m) :
    ∀ j : ℕ, j < n → j ≠ k →
      threeGap_natFract α u ≤ threeGap_distance α k j := by
  intro j hj hjk
  by_cases hforward : k < j
  · rw [threeGap_distance_of_le α hforward.le]
    apply humin (j - k) <;> omega
  · have hback : j < k := by omega
    rw [threeGap_distance_of_lt α hα hback]
    by_contra hlower
    have hlt : 1 - threeGap_natFract α (k - j) < threeGap_natFract α u :=
      lt_of_not_ge hlower
    have hsum : 1 ≤ threeGap_natFract α (k - j) + threeGap_natFract α u := by
      linarith
    have hadd : threeGap_natFract α ((k - j) + u) =
        threeGap_natFract α (k - j) + threeGap_natFract α u - 1 := by
      simpa [threeGap_natFract] using
        threeGap_fract_add_of_one_le α ((k - j : ℕ) : ℤ) (u : ℤ) hsum
    have hmin := humin ((k - j) + u) (by omega) (by omega)
    have hfrac_lt : threeGap_natFract α (k - j) < 1 := Int.fract_lt_one _
    rw [hadd] at hmin
    linarith

private theorem threeGap_backward_lower (n v k : ℕ) (α : ℝ) (hα : Irrational α)
    (hv : 1 ≤ v) (hk : k < n) (hvk : v ≤ k)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v) :
    ∀ j : ℕ, j < n → j ≠ k →
      1 - threeGap_natFract α v ≤ threeGap_distance α k j := by
  intro j hj hjk
  by_cases hback : j < k
  · rw [threeGap_distance_of_lt α hα hback]
    have hmax := hvmax (k - j) (by omega) (by omega)
    linarith
  · have hforward : k < j := by omega
    rw [threeGap_distance_of_le α hforward.le]
    by_contra hlower
    have hlt : threeGap_natFract α (j - k) < 1 - threeGap_natFract α v :=
      lt_of_not_ge hlower
    have hsum : threeGap_natFract α v + threeGap_natFract α (j - k) < 1 := by
      linarith
    have hadd : threeGap_natFract α (v + (j - k)) =
        threeGap_natFract α v + threeGap_natFract α (j - k) := by
      simpa [threeGap_natFract] using
        threeGap_fract_add_of_lt_one α (v : ℤ) ((j - k : ℕ) : ℤ) hsum
    have hmax := hvmax (v + (j - k)) (by omega) (by omega)
    have hm0 : ((j - k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : j - k ≠ 0)
    have hmpos : 0 < threeGap_natFract α (j - k) :=
      threeGap_fract_pos α hα hm0
    rw [hadd] at hmax
    linarith

private theorem threeGap_middle_fract_lt (n u v k : ℕ) (α : ℝ) (hα : Irrational α)
    (hu_lt : u < n) (hv : 1 ≤ v) (hv_lt : v < n) (hku : n ≤ k + u) (hkv : k < v)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v) :
    threeGap_natFract α u < threeGap_natFract α v := by
  have huv_ne : u ≠ v := by
    intro huv
    subst v
    have hu1 : threeGap_natFract α u = threeGap_natFract α 1 := le_antisymm
      (humin 1 (by omega) (by omega)) (hvmax 1 (by omega) (by omega))
    have : u = 1 := threeGap_natFract_injective α hα hu1
    omega
  exact lt_of_le_of_ne (humin v hv hv_lt)
    (fun h => huv_ne (threeGap_natFract_injective α hα h))

private theorem threeGap_middle_lower (n u v k : ℕ) (α : ℝ)
    (hα : Irrational α) (hu_lt : u < n) (hv : 1 ≤ v) (hv_lt : v < n)
    (hku : n ≤ k + u) (hkv : k < v)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v) :
    ∀ j : ℕ, j < n → j ≠ k →
      threeGap_natFract α u + (1 - threeGap_natFract α v) ≤
        threeGap_distance α k j := by
  have hfu_lt_fv : threeGap_natFract α u < threeGap_natFract α v :=
    threeGap_middle_fract_lt n u v k α hα hu_lt hv hv_lt hku hkv humin hvmax
  intro j hj hjk
  by_cases hforward : k < j
  · rw [threeGap_distance_of_le α hforward.le]
    have hm_lt_u : j - k < u := by omega
    have hfu_le_fm := humin (j - k) (by omega) (by omega)
    have hfu_lt_fm : threeGap_natFract α u < threeGap_natFract α (j - k) :=
      lt_of_le_of_ne hfu_le_fm (fun h => by
        have := threeGap_natFract_injective α hα h
        omega)
    have hsum : 1 ≤
        threeGap_natFract α (j - k) + threeGap_natFract α (u - (j - k)) := by
      by_contra h
      have hadd : threeGap_natFract α ((j - k) + (u - (j - k))) =
          threeGap_natFract α (j - k) + threeGap_natFract α (u - (j - k)) := by
        simpa [threeGap_natFract] using threeGap_fract_add_of_lt_one α
          ((j - k : ℕ) : ℤ) ((u - (j - k) : ℕ) : ℤ) (lt_of_not_ge h)
      have hnonneg : 0 ≤ threeGap_natFract α (u - (j - k)) := Int.fract_nonneg _
      rw [show (j - k) + (u - (j - k)) = u by omega] at hadd
      linarith
    have hadd : threeGap_natFract α ((j - k) + (u - (j - k))) =
        threeGap_natFract α (j - k) + threeGap_natFract α (u - (j - k)) - 1 := by
      simpa [threeGap_natFract] using threeGap_fract_add_of_one_le α
        ((j - k : ℕ) : ℤ) ((u - (j - k) : ℕ) : ℤ) hsum
    have hmax := hvmax (u - (j - k)) (by omega) (by omega)
    rw [show (j - k) + (u - (j - k)) = u by omega] at hadd
    linarith
  · have hback : j < k := by omega
    rw [threeGap_distance_of_lt α hα hback]
    have ha_lt_v : k - j < v := by omega
    have hfa_le_fv := hvmax (k - j) (by omega) (by omega)
    have hfa_lt_fv : threeGap_natFract α (k - j) < threeGap_natFract α v :=
      lt_of_le_of_ne hfa_le_fv (fun h => by
        have := threeGap_natFract_injective α hα h
        omega)
    have hsum : threeGap_natFract α (k - j) +
        threeGap_natFract α (v - (k - j)) < 1 := by
      by_contra h
      have hadd : threeGap_natFract α ((k - j) + (v - (k - j))) =
          threeGap_natFract α (k - j) + threeGap_natFract α (v - (k - j)) - 1 := by
        simpa [threeGap_natFract] using threeGap_fract_add_of_one_le α
          ((k - j : ℕ) : ℤ) ((v - (k - j) : ℕ) : ℤ) (le_of_not_gt h)
      have hlt : threeGap_natFract α (v - (k - j)) < 1 := Int.fract_lt_one _
      rw [show (k - j) + (v - (k - j)) = v by omega] at hadd
      linarith
    have hadd : threeGap_natFract α ((k - j) + (v - (k - j))) =
        threeGap_natFract α (k - j) + threeGap_natFract α (v - (k - j)) := by
      simpa [threeGap_natFract] using threeGap_fract_add_of_lt_one α
        ((k - j : ℕ) : ℤ) ((v - (k - j) : ℕ) : ℤ) hsum
    have hmin := humin (v - (k - j)) (by omega) (by omega)
    rw [show (k - j) + (v - (k - j)) = v by omega] at hadd
    linarith

private theorem threeGap_exists_successor (n u v k : ℕ) (α : ℝ) (hα : Irrational α)
    (hu_lt : u < n) (hv : 1 ≤ v) (hv_lt : v < n) (hk : k < n) (hsum : n ≤ u + v)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v) :
    ∃ j : ℕ, j < n ∧ j ≠ k ∧
      (threeGap_distance α k j = threeGap_natFract α u ∨
        threeGap_distance α k j = 1 - threeGap_natFract α v ∨
        threeGap_distance α k j =
          threeGap_natFract α u + (1 - threeGap_natFract α v)) ∧
      ∀ l : ℕ, l < n → l ≠ k →
        threeGap_distance α k j ≤ threeGap_distance α k l := by
  have hu : 1 ≤ u := by omega
  by_cases hforward : k + u < n
  · refine ⟨k + u, hforward, by omega, ?_, ?_⟩
    · left
      rw [threeGap_distance_of_le α (by omega)]
      congr 1
      omega
    · intro l hl hlk
      rw [threeGap_distance_of_le α (by omega)]
      have hlower := threeGap_forward_lower n u k α hα hu hforward humin l hl hlk
      simpa using hlower
  · have hku : n ≤ k + u := by omega
    by_cases hback : v ≤ k
    · refine ⟨k - v, by omega, by omega, ?_, ?_⟩
      · right
        left
        rw [threeGap_distance_of_lt α hα (by omega)]
        congr 2
        omega
      · intro l hl hlk
        rw [threeGap_distance_of_lt α hα (by omega)]
        have hlower := threeGap_backward_lower n v k α hα hv hk hback hvmax l hl hlk
        simpa only [show k - (k - v) = v by omega] using hlower
    · have hkv : k < v := by omega
      have hfu_lt_fv : threeGap_natFract α u < threeGap_natFract α v :=
        threeGap_middle_fract_lt n u v k α hα hu_lt hv hv_lt hku hkv humin hvmax
      have huv_ne : u ≠ v := fun h => by subst v; linarith
      refine ⟨k + u - v, by omega, by omega, ?_, ?_⟩
      · right
        right
        have heq : ((k + u - v : ℕ) : ℤ) - (k : ℤ) = (u : ℤ) - (v : ℤ) := by
          rw [Int.ofNat_sub (by omega : v ≤ k + u)]
          push_cast
          ring
        calc
          threeGap_distance α k (k + u - v) =
              threeGap_fract α ((u : ℤ) - (v : ℤ)) := by
            unfold threeGap_distance
            rw [heq]
          _ = 1 + threeGap_natFract α u - threeGap_natFract α v := by
            simpa [threeGap_natFract] using
              threeGap_fract_sub_of_lt α (u : ℤ) (v : ℤ) hfu_lt_fv
          _ = threeGap_natFract α u + (1 - threeGap_natFract α v) := by ring
      · intro l hl hlk
        have hlower := threeGap_middle_lower n u v k α hα hu_lt hv hv_lt hku hkv
          humin hvmax l hl hlk
        have heq : ((k + u - v : ℕ) : ℤ) - (k : ℤ) = (u : ℤ) - (v : ℤ) := by
          rw [Int.ofNat_sub (by omega : v ≤ k + u)]
          push_cast
          ring
        have hdist : threeGap_distance α k (k + u - v) =
            threeGap_natFract α u + (1 - threeGap_natFract α v) := by
          unfold threeGap_distance
          rw [heq]
          calc
            threeGap_fract α ((u : ℤ) - (v : ℤ)) =
                1 + threeGap_natFract α u - threeGap_natFract α v := by
              simpa [threeGap_natFract] using
                threeGap_fract_sub_of_lt α (u : ℤ) (v : ℤ) hfu_lt_fv
            _ = threeGap_natFract α u + (1 - threeGap_natFract α v) := by ring
        rw [hdist]
        exact hlower

/-- **Points of the three-gap configuration.** Let $n$ be a natural number and $\alpha$ a real
number, and write $\operatorname{frac}(t) = t - \lfloor t \rfloor$ for the fractional part of a
real number $t$. A real number $x$ is a three-gap point of $n$ and $\alpha$ if
$x = \operatorname{frac}(k\alpha)$ for some natural number $k < n$. -/
def IsThreeGapPoint (n : ℕ) (α x : ℝ) : Prop :=
  ∃ k : ℕ, k < n ∧ x = Int.fract ((k : ℝ) * α)

private theorem threeGap_isPoint_iff (n : ℕ) (α x : ℝ) :
    IsThreeGapPoint n α x ↔ ∃ k : ℕ, k < n ∧ x = threeGap_natFract α k := by
  constructor
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, hx.trans (threeGap_natFract_eq α k).symm⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, hx.trans (threeGap_natFract_eq α k)⟩

private theorem threeGap_isPoint_one_iff (α x : ℝ) :
    IsThreeGapPoint 1 α x ↔ x = 0 := by
  rw [threeGap_isPoint_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : k = 0 := by omega
    subst k
    simp [threeGap_natFract, threeGap_fract]
  · rintro rfl
    exact ⟨0, by omega, by simp [threeGap_natFract, threeGap_fract]⟩

/-- **Gap lengths of the three-gap configuration.** Let $n$ be a natural number and $\alpha$ a real
number. In this definition a point means a three-gap point of $n$ and $\alpha$, that is, a number
$\operatorname{frac}(k\alpha) = k\alpha - \lfloor k\alpha \rfloor$ for a natural number $k < n$.
A real number $d$ is a gap length of $n$ and $\alpha$ if either $d = y - x$ for points $x < y$
with no point strictly between $x$ and $y$, or there are a least point $x_{\min}$ and a greatest
point $x_{\max}$ and $d = 1 + x_{\min} - x_{\max}$. -/
def IsThreeGapLength (n : ℕ) (α d : ℝ) : Prop :=
  (∃ x y : ℝ, IsThreeGapPoint n α x ∧ IsThreeGapPoint n α y ∧ x < y ∧
    (∀ z : ℝ, IsThreeGapPoint n α z → x < z → z < y → False) ∧ d = y - x) ∨
  (∃ xlo xhi : ℝ, IsThreeGapPoint n α xlo ∧ IsThreeGapPoint n α xhi ∧
    (∀ z : ℝ, IsThreeGapPoint n α z → z ≤ xhi) ∧
    (∀ z : ℝ, IsThreeGapPoint n α z → xlo ≤ z) ∧ d = 1 + xlo - xhi)

private theorem threeGap_length_one_iff (α d : ℝ) :
    IsThreeGapLength 1 α d ↔ d = 1 := by
  constructor
  · rintro (⟨x, y, hpx, hpy, hxy, _hconsec, _hd⟩ |
      ⟨xlo, xhi, hplo, hphi, _hhi, _hlo, hd⟩)
    · rw [threeGap_isPoint_one_iff] at hpx hpy
      linarith
    · rw [threeGap_isPoint_one_iff] at hplo hphi
      linarith
  · intro hd
    right
    refine ⟨0, 0, (threeGap_isPoint_one_iff α 0).mpr rfl,
      (threeGap_isPoint_one_iff α 0).mpr rfl, ?_, ?_, ?_⟩
    · intro z hz
      rw [(threeGap_isPoint_one_iff α z).mp hz]
    · intro z hz
      rw [(threeGap_isPoint_one_iff α z).mp hz]
    · linarith

private theorem threeGap_linear_gap_le_distance (n : ℕ) (α : ℝ) (hα : Irrational α)
    {k j l : ℕ} (hl : l < n) (hlk : l ≠ k)
    (hconsec : ∀ t : ℕ, t < n →
      threeGap_natFract α k < threeGap_natFract α t →
      threeGap_natFract α t < threeGap_natFract α j → False) :
    threeGap_natFract α j - threeGap_natFract α k ≤ threeGap_distance α k l := by
  have hne : threeGap_natFract α l ≠ threeGap_natFract α k := fun h =>
    hlk (threeGap_natFract_injective α hα h)
  rcases lt_or_gt_of_ne hne with hbelow | habove
  · rw [threeGap_distance_eq_add_sub_of_value_lt α hbelow]
    have hjlt : threeGap_natFract α j < 1 := Int.fract_lt_one _
    have hlnonneg : 0 ≤ threeGap_natFract α l := Int.fract_nonneg _
    linarith
  · have hjl : threeGap_natFract α j ≤ threeGap_natFract α l := by
      by_contra h
      exact hconsec l hl habove (lt_of_not_ge h)
    rw [threeGap_distance_eq_sub_of_value_le α habove.le]
    linarith

private theorem threeGap_linear_length_cases (n u v : ℕ) (α : ℝ) (hα : Irrational α)
    (hu_lt : u < n) (hv : 1 ≤ v) (hv_lt : v < n) (hsum : n ≤ u + v)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v)
    {k j : ℕ} (hk : k < n) (hj : j < n)
    (hkj : threeGap_natFract α k < threeGap_natFract α j)
    (hconsec : ∀ t : ℕ, t < n →
      threeGap_natFract α k < threeGap_natFract α t →
      threeGap_natFract α t < threeGap_natFract α j → False) :
    threeGap_natFract α j - threeGap_natFract α k = threeGap_natFract α u ∨
      threeGap_natFract α j - threeGap_natFract α k = 1 - threeGap_natFract α v ∨
      threeGap_natFract α j - threeGap_natFract α k =
        threeGap_natFract α u + (1 - threeGap_natFract α v) := by
  obtain ⟨l, hl, hlk, hcase, hleast⟩ :=
    threeGap_exists_successor n u v k α hα hu_lt hv hv_lt hk hsum humin hvmax
  have hkj_ne : j ≠ k := fun h => by subst j; linarith
  have hupper := hleast j hj hkj_ne
  have hdistance : threeGap_distance α k j =
      threeGap_natFract α j - threeGap_natFract α k :=
    threeGap_distance_eq_sub_of_value_le α hkj.le
  have hlower := threeGap_linear_gap_le_distance n α hα hl hlk hconsec
  rw [hdistance] at hupper
  have heq : threeGap_distance α k l =
      threeGap_natFract α j - threeGap_natFract α k := le_antisymm hupper hlower
  rcases hcase with hcase | hcase | hcase
  · exact Or.inl (heq.symm.trans hcase)
  · exact Or.inr (Or.inl (heq.symm.trans hcase))
  · exact Or.inr (Or.inr (heq.symm.trans hcase))

private theorem threeGap_wrap_length_eq (n v : ℕ) (hn : 1 ≤ n) (α : ℝ)
    (hv_lt : v < n)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v)
    {xlo xhi d : ℝ} (hplo : IsThreeGapPoint n α xlo)
    (hphi : IsThreeGapPoint n α xhi)
    (hhi : ∀ z : ℝ, IsThreeGapPoint n α z → z ≤ xhi)
    (hlo : ∀ z : ℝ, IsThreeGapPoint n α z → xlo ≤ z)
    (hd : d = 1 + xlo - xhi) :
    d = 1 - threeGap_natFract α v := by
  obtain ⟨klo, hklo, hxlo⟩ := (threeGap_isPoint_iff n α xlo).mp hplo
  obtain ⟨khi, hkhi, hxhi⟩ := (threeGap_isPoint_iff n α xhi).mp hphi
  have hpzero : IsThreeGapPoint n α 0 := (threeGap_isPoint_iff n α 0).mpr
    ⟨0, by omega, by simp [threeGap_natFract, threeGap_fract]⟩
  have hxlo_le : xlo ≤ 0 := hlo 0 hpzero
  have hxlo_nonneg : 0 ≤ xlo := by
    rw [hxlo]
    exact Int.fract_nonneg _
  have hxlo_zero : xlo = 0 := le_antisymm hxlo_le hxlo_nonneg
  have hpv : IsThreeGapPoint n α (threeGap_natFract α v) :=
    (threeGap_isPoint_iff n α _).mpr ⟨v, hv_lt, rfl⟩
  have hv_le : threeGap_natFract α v ≤ xhi := hhi _ hpv
  have hxhi_le : xhi ≤ threeGap_natFract α v := by
    rw [hxhi]
    by_cases hkhi_zero : khi = 0
    · subst khi
      simp [threeGap_natFract, threeGap_fract, Int.fract_nonneg]
    · exact hvmax khi (by omega) hkhi
  have hxhi_eq : xhi = threeGap_natFract α v := le_antisymm hxhi_le hv_le
  rw [hd, hxlo_zero, hxhi_eq]
  ring

private theorem threeGap_length_cases (n u v : ℕ) (hn : 1 ≤ n) (α : ℝ)
    (hα : Irrational α) (hu_lt : u < n) (hv : 1 ≤ v) (hv_lt : v < n)
    (hsum : n ≤ u + v)
    (humin : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α u ≤ threeGap_natFract α m)
    (hvmax : ∀ m : ℕ, 1 ≤ m → m < n →
      threeGap_natFract α m ≤ threeGap_natFract α v)
    {d : ℝ} (hd : IsThreeGapLength n α d) :
    d = threeGap_natFract α u ∨ d = 1 - threeGap_natFract α v ∨
      d = threeGap_natFract α u + (1 - threeGap_natFract α v) := by
  rcases hd with hlinear | hwrap
  · obtain ⟨x, y, hpx, hpy, hxy, hconsec, hd⟩ := hlinear
    obtain ⟨k, hk, hx⟩ := (threeGap_isPoint_iff n α x).mp hpx
    obtain ⟨j, hj, hy⟩ := (threeGap_isPoint_iff n α y).mp hpy
    subst x
    subst y
    have hconsec' : ∀ t : ℕ, t < n →
        threeGap_natFract α k < threeGap_natFract α t →
        threeGap_natFract α t < threeGap_natFract α j → False := by
      intro t ht hkt htj
      exact hconsec (threeGap_natFract α t)
        ((threeGap_isPoint_iff n α _).mpr ⟨t, ht, rfl⟩) hkt htj
    have hcases := threeGap_linear_length_cases n u v α hα hu_lt hv hv_lt hsum
      humin hvmax hk hj hxy hconsec'
    rcases hcases with hcase | hcase | hcase
    · exact Or.inl (hd.trans hcase)
    · exact Or.inr (Or.inl (hd.trans hcase))
    · exact Or.inr (Or.inr (hd.trans hcase))
  · obtain ⟨xlo, xhi, hplo, hphi, hhi, hlo, hd⟩ := hwrap
    exact Or.inr (Or.inl
      (threeGap_wrap_length_eq n v hn α hv_lt hvmax hplo hphi hhi hlo hd))

/-- **Three-gap theorem.** Let $n \ge 1$ be a natural number and $\alpha$ an irrational real
number. Consider the points $\operatorname{frac}(k\alpha) = k\alpha - \lfloor k\alpha \rfloor$ for
$0 \le k < n$ on the circle $[0, 1)$. The set of gap lengths of $n$ and $\alpha$, that is, the
lengths of the gaps between cyclically consecutive points, including the gap that wraps around
from the greatest point to the least, is finite and has at most three elements. If it has exactly
three elements, the largest of them is the sum of the other two.

Proof: We formalize the standard successor argument of Sós (1958) and Świerczkowski (1959),
following Alessandri and Berthé, *Three distance theorems and combinatorics on words*, §2.

Proves `Wanted` entry `three_gap` (statement `three-gap-s1`).

Source: https://en.wikipedia.org/wiki/Three-gap_theorem.
-/
theorem three_gap (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : Irrational α) :
    ∃ G : Finset ℝ,
      (∀ d : ℝ, d ∈ G ↔ IsThreeGapLength n α d) ∧
      G.card ≤ 3 ∧
      (G.card = 3 → ∃ a b c : ℝ,
        a ∈ G ∧ b ∈ G ∧ c ∈ G ∧ a < b ∧ b < c ∧ c = a + b) := by
  classical
  by_cases hn_one : n = 1
  · subst n
    refine ⟨{1}, ?_, by simp, ?_⟩
    · intro d
      simp [threeGap_length_one_iff]
    · intro hcard
      norm_num at hcard
  · have hn_two : 2 ≤ n := by omega
    obtain ⟨u, v, hu, hu_lt, hv, hv_lt, humin, hvmax⟩ :=
      threeGap_exists_extrema n hn_two α
    have hsum : n ≤ u + v :=
      threeGap_extrema_sum_ge n u v α hα hu hv humin hvmax
    let δ₁ : ℝ := threeGap_natFract α u
    let δ₂ : ℝ := 1 - threeGap_natFract α v
    let T : Finset ℝ := {δ₁, δ₂, δ₁ + δ₂}
    let G : Finset ℝ := T.filter (IsThreeGapLength n α)
    refine ⟨G, ?_, ?_, ?_⟩
    · intro d
      constructor
      · intro hd
        exact (Finset.mem_filter.mp (by simpa [G] using hd)).2
      · intro hd
        apply Finset.mem_filter.mpr
        refine ⟨?_, hd⟩
        have hcases := threeGap_length_cases n u v hn α hα hu_lt hv hv_lt hsum
          humin hvmax hd
        change d ∈ T
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        simpa only [δ₁, δ₂] using hcases
    · have hfilter : G.card ≤ T.card := by
        simpa [G] using Finset.card_filter_le T (IsThreeGapLength n α)
      exact hfilter.trans Finset.card_le_three
    · intro hcard
      have hGT : G ⊆ T := by
        exact Finset.filter_subset (IsThreeGapLength n α) T
      have hTleG : T.card ≤ G.card := by
        rw [hcard]
        exact Finset.card_le_three
      have hGT_eq : G = T := Finset.eq_of_subset_of_card_le hGT hTleG
      have hTcard : T.card = 3 := by rw [← hGT_eq, hcard]
      have hu0 : (u : ℤ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
      have hδ₁pos : 0 < δ₁ := by
        exact threeGap_fract_pos α hα hu0
      have hδ₂pos : 0 < δ₂ := by
        have hfvlt : threeGap_natFract α v < 1 := Int.fract_lt_one _
        dsimp [δ₂]
        linarith
      have hδne : δ₁ ≠ δ₂ := by
        intro heq
        have hsmall : ({δ₁, δ₁ + δ₁} : Finset ℝ).card ≤ 2 := by
          calc
            ({δ₁, δ₁ + δ₁} : Finset ℝ).card ≤
                ({δ₁ + δ₁} : Finset ℝ).card + 1 := Finset.card_insert_le _ _
            _ = 2 := by simp
        have hTsmall : T = {δ₁, δ₁ + δ₁} := by simp [T, heq]
        have hsmallcard : ({δ₁, δ₁ + δ₁} : Finset ℝ).card = 3 := by
          rw [← hTsmall]
          exact hTcard
        omega
      have hδ₁mem : δ₁ ∈ G := by rw [hGT_eq]; simp [T]
      have hδ₂mem : δ₂ ∈ G := by rw [hGT_eq]; simp [T]
      have hδsummem : δ₁ + δ₂ ∈ G := by rw [hGT_eq]; simp [T]
      by_cases hδlt : δ₁ < δ₂
      · exact ⟨δ₁, δ₂, δ₁ + δ₂, hδ₁mem, hδ₂mem, hδsummem, hδlt,
          by linarith, rfl⟩
      · have hδgt : δ₂ < δ₁ := lt_of_le_of_ne (le_of_not_gt hδlt) hδne.symm
        exact ⟨δ₂, δ₁, δ₁ + δ₂, hδ₂mem, hδ₁mem, hδsummem, hδgt,
          by linarith, by ring⟩

end MetaMathlibExt
