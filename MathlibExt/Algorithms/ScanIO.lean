/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# External-memory scanning

Block transfers for scanning a list in consecutive blocks.
Scanning `N` items in blocks of size `B` costs
`ceil(N / B)` transfers. External merge sort and B-tree
bounds are not included here.
-/

@[expose] public section

/-- Block transfers for scanning a list (ALG-28 core).
`blocks B l` counts block reads when a scan reads `l` in
consecutive blocks of size `B`, starting at a block
boundary; it is `0` for `B = 0`. -/
def blocks (B : ℕ) {α : Type*} : List α → ℕ
  | [] => 0
  | a :: xs => if B = 0 then 0 else 1 + blocks B (List.drop B (a :: xs))
termination_by l => l.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

private theorem blocks_nil (B : ℕ) {α : Type*} : blocks B ([] : List α) = 0 := by
  simp only [blocks]

private theorem blocks_cons (B : ℕ) {α : Type*} (a : α) (xs : List α) (hB : 0 < B) :
    blocks B (a :: xs) = 1 + blocks B (List.drop B (a :: xs)) := by
  simp only [blocks, if_neg (Nat.pos_iff_ne_zero.mp hB)]

private theorem div_pred_self (B : ℕ) (hB : 0 < B) : (B - 1) / B = 0 :=
  Nat.div_eq_of_lt (by omega)

private theorem arith_key (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    1 + (m - B + B - 1) / B = (m + B - 1) / B := by
  rcases le_total m B with h | h
  · have hsub : m - B = 0 := Nat.sub_eq_zero_of_le h
    rw [hsub, Nat.zero_add, div_pred_self B hB]
    have hlo : 1 * B ≤ m + B - 1 := by omega
    have hhi : m + B - 1 < (1 + 1) * B := by omega
    have hone : (m + B - 1) / B = 1 :=
      Nat.div_eq_of_lt_le (k := 1) (n := B) (m := m + B - 1) hlo hhi
    omega
  · have hcancel : m - B + B = m := Nat.sub_add_cancel h
    rw [hcancel]
    have hrewrite : m + B - 1 = (m - 1) + B := by omega
    rw [hrewrite]
    have hadd : ((m - 1) + B) / B = (m - 1) / B + 1 := by
      have h1 : (m - 1) + B = (m - 1) + 1 * B := by rw [Nat.one_mul]
      rw [h1]
      exact Nat.add_mul_div_right _ _ hB
    rw [hadd]
    omega

/-- Scanning `N` items costs `⌈N / B⌉` block transfers. -/
theorem blocks_length (B : ℕ) {α : Type*} (l : List α) (hB : 0 < B) :
    blocks B l = (l.length + B - 1) / B := by
  have key : ∀ (n : ℕ) (l : List α), l.length < n → blocks B l = (l.length + B - 1) / B := by
    intro n
    induction n with
    | zero =>
      intro l hl
      omega
    | succ n ih =>
      intro l hl
      cases l with
      | nil =>
        rw [blocks_nil B]
        have h0 : ([] : List α).length = 0 := rfl
        rw [h0, Nat.zero_add]
        exact (div_pred_self B hB).symm
      | cons a xs =>
        have hlen : (a :: xs).length = xs.length + 1 := rfl
        have hdrop : (List.drop B (a :: xs)).length < n := by
          rw [List.length_drop]
          omega
        have hIH := ih (List.drop B (a :: xs)) hdrop
        rw [List.length_drop] at hIH
        rw [blocks_cons B a xs hB, hIH]
        have hm : 0 < (a :: xs).length := by omega
        exact arith_key _ _ hm hB
  exact key (l.length + 1) l (Nat.lt_succ_self _)

end
