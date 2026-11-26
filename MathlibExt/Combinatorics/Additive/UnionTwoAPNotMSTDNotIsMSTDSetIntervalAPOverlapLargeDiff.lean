/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An interval and a progression with large integer step

We compare sums and differences by counting cross-differences with positive step index.
-/

namespace MetaMathlibExt

open scoped Pointwise

private theorem not_int_of_not_nat (x : ℝ) (hx : 0 < x)
    (hxN : x ∉ Set.range ((↑) : ℕ → ℝ)) (k : ℤ) : x ≠ k := by
  intro h
  have hk : 0 ≤ k := by exact_mod_cast (show (0 : ℝ) ≤ k by linarith)
  apply hxN
  refine ⟨k.toNat, ?_⟩
  have heq := Int.toNat_of_nonneg hk
  have : (k.toNat : ℝ) = k := by exact_mod_cast heq
  exact this.trans h.symm

private theorem signed_card_le (A S : Finset ℝ) (hzero : 0 ∈ A)
    (hS : S ⊆ A - A) (hpos : ∀ z ∈ S, 0 < z) :
    2 * S.card + 1 ≤ (A - A).card := by
  classical
  let N := S.image fun z => -z
  have hSN : Disjoint S N := by
    rw [Finset.disjoint_left]
    intro z hz hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    have := hpos w hw
    have := hpos (-w) hz
    linarith
  have hZ : Disjoint (S ∪ N) {0} := by
    rw [Finset.disjoint_left]
    intro z hz hz0
    have : z = 0 := Finset.mem_singleton.mp hz0
    subst z
    rcases Finset.mem_union.mp hz with hz | hz
    · have := hpos 0 hz
      linarith
    · obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hz
      have := hpos w hw
      linarith
  have hsub : (S ∪ N) ∪ {0} ⊆ A - A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact hS hz
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp (hS hw)
        exact Finset.mem_sub.mpr ⟨b, hb, a, ha, by ring⟩
    · have : z = 0 := Finset.mem_singleton.mp hz
      subst z
      exact Finset.mem_sub.mpr ⟨0, hzero, 0, hzero, by ring⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hZ, Finset.card_union_of_disjoint hSN,
    Finset.card_singleton] at h
  have hN : N.card = S.card := Finset.card_image_of_injective _ neg_injective
  omega

private theorem sum_card_le (n m : ℕ) (x d : ℝ) :
    ((realIntervalSet n ∪ realAPSet x m d) +
      (realIntervalSet n ∪ realAPSet x m d)).card ≤
      (2 * n - 1) + n * (m + 1) + (2 * m + 1) := by
  classical
  let s₀ := (Finset.range (2 * n - 1)).image fun k : ℕ => (k : ℝ)
  let s₁ := (Finset.range n ×ˢ Finset.range (m + 1)).image
    fun p : ℕ × ℕ => (p.1 : ℝ) + (x + p.2 * d)
  let s₂ := (Finset.range (2 * m + 1)).image fun k : ℕ => 2 * x + k * d
  have hs : (realIntervalSet n ∪ realAPSet x m d) +
      (realIntervalSet n ∪ realAPSet x m d) ⊆ (s₀ ∪ s₁) ∪ s₂ := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr (by omega), by simp⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(j, i), Finset.mem_product.mpr ⟨hj, hi⟩, by ring⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr (by omega), by
        push_cast
        ring⟩
  have h₀ : s₀.card ≤ 2 * n - 1 := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  have h₁ : s₁.card ≤ n * (m + 1) := by
    exact (Finset.card_image_le).trans_eq (by simp)
  have h₂ : s₂.card ≤ 2 * m + 1 := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  have := Finset.card_le_card hs
  have := Finset.card_union_le s₀ s₁
  have := Finset.card_union_le (s₀ ∪ s₁) s₂
  omega

/-- **Interval plus progression with non-integer start and integer step at least $n$ is not MSTD.**
Let $n \ge 3$, $m \ge 2$ and $d \ge n$ be natural numbers, and let $x$ be a real number with
$0 < x < n - 1$ that is not a natural number. Write $I_n = \{0, 1, \dots, n - 1\}$ and
$J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 17
(`integers-2026-A58-lem-17`). -/
public theorem not_isMSTDSet_intervalAP_overlap_large_diff (n m d : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : n ≤ d)
    (hxN : x ∉ Set.range ((↑) : ℕ → ℝ)) (hx₀ : 0 < x) (hx₁ : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ)) := by
  classical
  let A := realIntervalSet n ∪ realAPSet x m (d : ℝ)
  let P := (Finset.range (n - 1)).image fun i : ℕ => (i : ℝ) + 1
  let Q := (Finset.range m).image fun j : ℕ => ((j : ℝ) + 1) * d
  let C := (Finset.range n ×ˢ Finset.range m).image
    fun p : ℕ × ℕ => x + ((p.2 : ℝ) + 1) * d - p.1
  have hx : 0 < x ∧ x < (n : ℝ) - 1 := ⟨hx₀, hx₁⟩
  have hdn : (n : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have memI (i : ℕ) (hi : i < n) : (i : ℝ) ∈ A :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
  have memJ (j : ℕ) (hj : j ≤ m) : x + j * (d : ℝ) ∈ A :=
    Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  have hzero : 0 ∈ A := by simpa using memI 0 (by omega)
  have hP : P.card = n - 1 := by
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro i j h
    exact_mod_cast add_right_cancel h
  have hQ : Q.card = m := by
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro i j h
    exact_mod_cast add_right_cancel (mul_right_cancel₀ (ne_of_gt hdpos) h)
  have hC : C.card = n * m := by
    rw [Finset.card_image_iff.mpr ?_, Finset.card_product, Finset.card_range,
      Finset.card_range]
    intro p hp q hq heq
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    have hpR : (p.1 : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hp₁
    have hqR : (q.1 : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hq₁
    have hp0 : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ q.1 := Nat.cast_nonneg _
    have h₂ : p.2 = q.2 := by
      rcases lt_trichotomy p.2 q.2 with hlt | he | hgt
      · have hgap : (p.2 : ℝ) + 1 ≤ q.2 := by exact_mod_cast hlt
        have := mul_le_mul_of_nonneg_right hgap (le_of_lt hdpos)
        change x + ((p.2 : ℝ) + 1) * d - p.1 =
          x + ((q.2 : ℝ) + 1) * d - q.1 at heq
        nlinarith
      · exact he
      · have hgap : (q.2 : ℝ) + 1 ≤ p.2 := by exact_mod_cast hgt
        have := mul_le_mul_of_nonneg_right hgap (le_of_lt hdpos)
        change x + ((p.2 : ℝ) + 1) * d - p.1 =
          x + ((q.2 : ℝ) + 1) * d - q.1 at heq
        nlinarith
    have h₁ : p.1 = q.1 := by
      change x + ((p.2 : ℝ) + 1) * d - p.1 =
        x + ((q.2 : ℝ) + 1) * d - q.1 at heq
      rw [h₂] at heq
      exact_mod_cast (sub_right_inj.mp heq)
    exact Prod.ext h₁ h₂
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hz'
    have hi' := Finset.mem_range.mp hi
    have hiR : (i : ℝ) + 1 < n := by exact_mod_cast (show i + 1 < n by omega)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    change ((j : ℝ) + 1) * d = (i : ℝ) + 1 at heq
    nlinarith
  have hPC : Disjoint P C := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨a, j⟩, haj, heq⟩ := Finset.mem_image.mp hz'
    apply not_int_of_not_nat x hx.1 hxN ((i : ℤ) + 1 - ((j : ℤ) + 1) * d + a)
    change x + ((j : ℝ) + 1) * d - a = (i : ℝ) + 1 at heq
    push_cast
    linarith
  have hQC : Disjoint Q C := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨a, j⟩, haj, heq⟩ := Finset.mem_image.mp hz'
    apply not_int_of_not_nat x hx.1 hxN (((i : ℤ) + 1) * d - ((j : ℤ) + 1) * d + a)
    change x + ((j : ℝ) + 1) * d - a = ((i : ℝ) + 1) * d at heq
    push_cast
    linarith
  have hpos : ∀ z ∈ (P ∪ Q) ∪ C, 0 < z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        positivity
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        exact mul_pos (by positivity) hdpos
    · obtain ⟨⟨a, j⟩, haj, rfl⟩ := Finset.mem_image.mp hz
      have haR : (a : ℝ) < n := by
        exact_mod_cast Finset.mem_range.mp (Finset.mem_product.mp haj).1
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      change 0 < x + ((j : ℝ) + 1) * d - a
      nlinarith [hx.1]
  have hsub : (P ∪ Q) ∪ C ⊆ A - A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        have hi' := Finset.mem_range.mp hi
        exact Finset.mem_sub.mpr ⟨(i + 1 : ℕ), memI (i + 1) (by omega),
          0, hzero, by push_cast; ring⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_sub.mpr ⟨x + (j + 1 : ℕ) * (d : ℝ), memJ (j + 1) (by omega),
          x, by simpa using memJ 0 (by omega), by push_cast; ring⟩
    · obtain ⟨⟨a, j⟩, haj, rfl⟩ := Finset.mem_image.mp hz
      have ha := Finset.mem_range.mp (Finset.mem_product.mp haj).1
      have hj := Finset.mem_range.mp (Finset.mem_product.mp haj).2
      exact Finset.mem_sub.mpr ⟨x + (j + 1 : ℕ) * (d : ℝ), memJ (j + 1) (by omega),
        (a : ℝ), memI a ha, by push_cast; ring⟩
  have hdiff := signed_card_le A ((P ∪ Q) ∪ C) hzero hsub hpos
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hPC, hQC⟩),
    Finset.card_union_of_disjoint hPQ, hP, hQ, hC] at hdiff
  have hsum := sum_card_le n m x (d : ℝ)
  change (A + A).card ≤ (2 * n - 1) + n * (m + 1) + (2 * m + 1) at hsum
  have hnm := Nat.mul_le_mul_left n hm
  rw [Nat.mul_add, Nat.mul_one] at hsum
  rw [Nat.mul_comm n 2, two_mul] at hnm
  change ¬ (A - A).card < (A + A).card
  omega

end MetaMathlibExt
