/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.EvenOddCompositions
import Mathlib.Data.Fintype.BigOperators

/-!
# Signed counts of compositions with parts greater than one

Deleting a leading two reverses the sign. Decreasing a larger leading part by one preserves
it. This gives a two-term recurrence for the signed count and hence a sign change every
three steps.
-/

namespace MetaMathlibExt

private abbrev Large (n : ℕ) := {c : Composition n // ∀ a ∈ c.blocks, 1 < a}

private def mkLarge {n : ℕ} (xs : List ℕ) (h : ∀ a ∈ xs, 1 < a) (hsum : xs.sum = n) :
    Large n :=
  ⟨⟨xs, fun ha => Nat.zero_lt_of_lt (h _ ha), hsum⟩, h⟩

private def prependTwo {n : ℕ} (c : Large n) : Large (n + 2) :=
  mkLarge (2 :: c.val.blocks) (List.forall_mem_cons.mpr ⟨by decide, c.property⟩)
    (by simp [Nat.add_comm])

private def increaseHead (n : ℕ) : Large (n + 1) → Large (n + 2)
  | ⟨⟨[], _, hsum⟩, _⟩ => False.elim (by simp at hsum)
  | ⟨⟨a :: xs, _, hsum⟩, h⟩ =>
    mkLarge ((a + 1) :: xs)
      (List.forall_mem_cons.mpr ⟨Nat.lt_succ_of_lt (h a List.mem_cons_self),
        fun b hb => h b (List.mem_cons_of_mem _ hb)⟩)
      (by simp only [List.sum_cons] at hsum ⊢; omega)

private def splitLarge (n : ℕ) : Large (n + 2) → Large n ⊕ Large (n + 1)
  | ⟨⟨[], _, hsum⟩, _⟩ => False.elim (by simp at hsum)
  | ⟨⟨0 :: _, _, _⟩, h⟩ => False.elim (by simpa using h 0 List.mem_cons_self)
  | ⟨⟨1 :: _, _, _⟩, h⟩ => False.elim (by simpa using h 1 List.mem_cons_self)
  | ⟨⟨2 :: xs, _, hsum⟩, h⟩ =>
    .inl (mkLarge xs (fun b hb => h b (List.mem_cons_of_mem _ hb))
      (by simp only [List.sum_cons] at hsum; omega))
  | ⟨⟨(a + 3) :: xs, _, hsum⟩, h⟩ =>
    .inr (mkLarge ((a + 2) :: xs)
      (List.forall_mem_cons.mpr ⟨by omega, fun b hb => h b (List.mem_cons_of_mem _ hb)⟩)
      (by simp only [List.sum_cons] at hsum ⊢; omega))

private def largeEquiv (n : ℕ) : Large n ⊕ Large (n + 1) ≃ Large (n + 2) where
  toFun := Sum.elim prependTwo (increaseHead n)
  invFun := splitLarge n
  left_inv := by
    rintro (⟨⟨xs, _, _⟩, _⟩ | ⟨⟨xs, _, hsum⟩, h⟩)
    · rfl
    · cases xs with
      | nil => simp at hsum
      | cons a xs =>
        have ha := h a List.mem_cons_self
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
        rfl
  right_inv := by
    rintro ⟨⟨xs, _, hsum⟩, h⟩
    cases xs with
    | nil => simp at hsum
    | cons a xs =>
      have ha := h a List.mem_cons_self
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
      cases b <;> rfl

private noncomputable def signedLargeCount (n : ℕ) : ℤ :=
  compositionOddMinusEven n (fun c => ∀ a ∈ c.blocks, 1 < a)

open Classical in
private theorem signedLargeCount_eq_sum (n : ℕ) :
    signedLargeCount n = ∑ c : Large n, (-1 : ℤ) ^ (c.val.length + 1) := by
  rw [signedLargeCount, compositionOddMinusEven, ← Finset.subtype_univ,
    Finset.sum_subtype_eq_sum_filter (p := fun c : Composition n => ∀ a ∈ c.blocks, 1 < a)
      (fun c => (-1 : ℤ) ^ (c.length + 1)), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> rfl

private theorem signedLargeCount_add_two (n : ℕ) :
    signedLargeCount (n + 2) = signedLargeCount (n + 1) - signedLargeCount n := by
  classical
  simp only [signedLargeCount_eq_sum]
  rw [← (largeEquiv n).sum_comp, Fintype.sum_sum_type, sub_eq_neg_add,
    ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro c _
    change (-1 : ℤ) ^ (c.val.length + 1 + 1) = -((-1) ^ (c.val.length + 1))
    simp [pow_succ]
  · apply Finset.sum_congr rfl
    intro c _
    change (-1 : ℤ) ^ ((increaseHead n c).val.length + 1) = (-1) ^ (c.val.length + 1)
    obtain ⟨⟨xs, _, hsum⟩, _⟩ := c
    cases xs with
    | nil => simp at hsum
    | cons a xs => rfl

private theorem signedLargeCount_zero : signedLargeCount 0 = -1 := by
  unfold signedLargeCount
  rw [show (fun c : Composition 0 => ∀ a ∈ c.blocks, 1 < a) = (fun _ => True) from
    funext fun c => by simp [c.blocks_eq_nil.mpr rfl]]
  exact compositionOddMinusEven_zero_true

private theorem signedLargeCount_one : signedLargeCount 1 = 0 := by
  unfold signedLargeCount compositionOddMinusEven
  apply Finset.sum_eq_zero
  intro c _
  have hc : ¬ ∀ a ∈ c.blocks, 1 < a := by
    intro h
    cases hb : c.blocks with
    | nil => simp at hb
    | cons a xs =>
      have ha : a ∈ c.blocks := by simp [hb]
      exact (not_lt_of_ge (c.blocks_le ha)) (h a ha)
  simp [hc]

private theorem signedLargeCount_add_three (n : ℕ) :
    signedLargeCount (n + 3) = -signedLargeCount n := by
  rw [signedLargeCount_add_two (n + 1), signedLargeCount_add_two n]
  omega

private theorem signedLargeCount_period (j r : ℕ) :
    signedLargeCount (3 * j + r) = signedLargeCount r * (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 3 * (j + 1) + r = (3 * j + r) + 3 by omega,
      signedLargeCount_add_three, ih, pow_succ, ← mul_assoc, mul_neg_one]

/-- **Signed count of compositions with parts greater than one.** For every $n \ge 0$, among the
compositions of $n + 1$ whose parts are all greater than $1$, the number with an odd number of
parts minus the number with an even number of parts is $(-1)^j$ if $n = 3j + 1$ or $n = 3j + 2$
for some $j \ge 0$, and $0$ otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 5
(`jis-2024-24.6.5-thm-5`). -/
public theorem compositionOddMinusEven_parts_gt_one (n : ℕ) :
    (∀ j : ℕ, n = 3 * j + 1 ∨ n = 3 * j + 2 →
        compositionOddMinusEven (n + 1) (fun c => ∀ a ∈ c.blocks, 1 < a) = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ 3 * j + 1 ∧ n ≠ 3 * j + 2) →
        compositionOddMinusEven (n + 1) (fun c => ∀ a ∈ c.blocks, 1 < a) = 0) := by
  have htwo : signedLargeCount 2 = 1 := by
    simpa [signedLargeCount_zero, signedLargeCount_one] using signedLargeCount_add_two 0
  have hthree : signedLargeCount 3 = 1 := by
    simpa [signedLargeCount_zero] using signedLargeCount_add_three 0
  constructor
  · intro j hj
    change signedLargeCount (n + 1) = (-1) ^ j
    rcases hj with rfl | rfl
    · rw [signedLargeCount_period j 2, htwo, one_mul]
    · rw [signedLargeCount_period j 3, hthree, one_mul]
  · intro h
    change signedLargeCount (n + 1) = 0
    have h₁ := (h (n / 3)).1
    have h₂ := (h (n / 3)).2
    rw [show n + 1 = 3 * (n / 3) + 1 by omega,
      signedLargeCount_period, signedLargeCount_one, zero_mul]

end MetaMathlibExt
