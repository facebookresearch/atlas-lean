/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Support

/-!
# Counting the ranks and dummy inputs of a compact circuit

A valid input gate can find its new variable number by counting the distinct
active labels strictly below its old label. The size of the dummy pool can be
computed by testing at most one candidate per active variable, using addition
and comparison of binary fields.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support

private theorem sorted_idxOf (l : List ℕ) (i : ℕ) (hs : l.Pairwise (· < ·)) (hm : i ∈ l) :
    l.idxOf i = (l.filter (· < i)).length := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    have horder := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hm with eq | tail
    · subst i
      have hf : l.filter (· < a) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        have := horder.1 b hb
        simp only [decide_eq_true_eq]
        omega
      simp [hf]
    · have hl := horder.1 i tail
      have he : (a == i) = false := by simp [Nat.ne_of_lt hl]
      simp [List.idxOf_cons, he, hl, ih horder.2 tail]

/-- On an active variable, the sorted numbering has rank equal to the
number of smaller active labels. Every dummy label comes after them. -/
theorem index_count (n k : ℕ) (C : List WCGate) {i : ℕ} (hi : i ∈ active n C) :
    (labels n k C).idxOf i = ((active n C).filter (· < i)).card := by
  let L := labels n k C
  have ltN : i < n := Finset.mem_range.mp (active_subset n C hi)
  have mem : i ∈ L := by
    change i ∈ (compactUniverse n k (active n C)).sort
    exact (Finset.mem_sort _).mpr (Finset.mem_union_left _ hi)
  have order : L.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  rw [sorted_idxOf _ _ order mem]
  have eq : (L.filter (· < i)).toFinset = (active n C).filter (· < i) := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter]
    have : j ∈ L ↔ j ∈ active n C ∨
        ∃ v < dummyCount n (active n C).card k, n + v = j := by
      simp [L, labels, compactUniverse]
    rw [this]
    constructor
    · rintro ⟨h | ⟨v, hv, rfl⟩, hj⟩
      · exact ⟨h, hj⟩
      · omega
    · exact fun h => ⟨Or.inl h.1, h.2⟩
  rw [← eq]
  exact (List.toFinset_card_of_nodup ((Finset.sort_nodup ..).filter _)).symm

/-- Natural numbers below the dummy count are recognized by these two
comparisons. The scanned range has length equal to the active set's size. -/
theorem dummyCount_eq_filter {n k m : ℕ} (hm : m ≤ n) :
    dummyCount n m k =
      ((List.range m).filter (fun j => decide
        (j < min k m ∧ k + m + j < n + min k m))).length := by
  let xs := (List.range m).filter (fun j => decide (j < min k m ∧ k + m + j < n + min k m))
  have he : xs.toFinset = Finset.range (dummyCount n m k) := by
    ext i
    simp only [xs, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
      Finset.mem_range, dummyCount]
    omega
  have hn : xs.Nodup := List.nodup_range.filter _
  rw [← Finset.card_range (dummyCount n m k), ← he]
  exact List.toFinset_card_of_nodup hn

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support
