/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Count
import Mathlib.Tactic.Linarith

/-!
# Misra-Gries heavy hitters

The Misra-Gries summary keeps at most `k - 1` positive counters.
Processing an item increments its counter when it is positive or
a slot is free; otherwise every counter is decremented. This
module proves the deterministic guarantees: counters never
exceed true frequencies, frequencies exceed counters by at most
the number of decrement rounds, and the resulting error bound.
-/

@[expose] public section

/-- Misra-Gries heavy hitters with parameter `k` (core of
ALG-26b): state is a counter map plus a count of decrement-all
rounds. Processing `x`: increment its counter when it is
positive or fewer than `k - 1` counters are positive; otherwise
decrement every counter and record a round. -/
noncomputable def mgStep {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (x : X) : (X → ℕ) × ℕ :=
  if st.1 x > 0 ∨ (Finset.univ.filter (fun y => 0 < st.1 y)).card < k - 1
  then (Function.update st.1 x (st.1 x + 1), st.2)
  else (fun y => st.1 y - 1, st.2 + 1)

/-- Run Misra-Gries over a stream. -/
noncomputable def mgRun {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) : (X → ℕ) × ℕ :=
  s.foldl (mgStep k) (fun _ => 0, 0)

private theorem mgStep_le_same {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (a : X) :
    (mgStep k st a).1 a ≤ st.1 a + 1 := by
  unfold mgStep
  split_ifs
  · show Function.update st.1 a (st.1 a + 1) a ≤ st.1 a + 1
    rw [Function.update_self]
  · show st.1 a - 1 ≤ st.1 a + 1
    omega

private theorem mgStep_le_other {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (a x : X) (h : x ≠ a) :
    (mgStep k st a).1 x ≤ st.1 x := by
  unfold mgStep
  split_ifs
  · show Function.update st.1 a (st.1 a + 1) x ≤ st.1 x
    have hu : Function.update st.1 a (st.1 a + 1) x = st.1 x :=
      Function.update_of_ne h _ _
    rw [hu]
  · show st.1 x - 1 ≤ st.1 x
    exact Nat.sub_le _ _

private theorem mgFold_le {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) (st : (X → ℕ) × ℕ) (x : X) :
    (List.foldl (mgStep k) st s).1 x ≤ st.1 x + s.count x := by
  induction s generalizing st with
  | nil =>
    rw [List.foldl_nil, List.count_nil]
    omega
  | cons a s ih =>
    rw [List.foldl_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [List.count_cons_self]
      have hstep := mgStep_le_same k st x
      have hih := ih (mgStep k st x)
      omega
    · have hne : a ≠ x := fun h => hxa h.symm
      rw [List.count_cons_of_ne hne]
      have hstep := mgStep_le_other k st a x hxa
      have hih := ih (mgStep k st a)
      omega

/-- Counters never exceed true frequencies. -/
theorem mg_le_freq {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) (x : X) :
    (mgRun k s).1 x ≤ s.count x := by
  have h := mgFold_le k s (fun _ => 0, 0) x
  simpa [mgRun] using h

private theorem mgStep_ge_same {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (a : X) :
    st.1 a + 1 + st.2 ≤ (mgStep k st a).1 a + (mgStep k st a).2 := by
  unfold mgStep
  split_ifs with hc
  · show st.1 a + 1 + st.2 ≤ Function.update st.1 a (st.1 a + 1) a + st.2
    rw [Function.update_self]
  · show st.1 a + 1 + st.2 ≤ (st.1 a - 1) + (st.2 + 1)
    have hnot : ¬ st.1 a > 0 := fun h => hc (Or.inl h)
    omega

private theorem mgStep_ge_other {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (a x : X) (h : x ≠ a) :
    st.1 x + st.2 ≤ (mgStep k st a).1 x + (mgStep k st a).2 := by
  unfold mgStep
  split_ifs
  · show st.1 x + st.2 ≤ Function.update st.1 a (st.1 a + 1) x + st.2
    have hu : Function.update st.1 a (st.1 a + 1) x = st.1 x :=
      Function.update_of_ne h _ _
    rw [hu]
  · show st.1 x + st.2 ≤ (st.1 x - 1) + (st.2 + 1)
    omega

private theorem mgFold_ge {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) (st : (X → ℕ) × ℕ) (x : X) :
    s.count x + st.1 x + st.2
      ≤ (List.foldl (mgStep k) st s).1 x + (List.foldl (mgStep k) st s).2 := by
  induction s generalizing st with
  | nil =>
    rw [List.foldl_nil, List.count_nil]
    omega
  | cons a s ih =>
    rw [List.foldl_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [List.count_cons_self]
      have hstep := mgStep_ge_same k st x
      have hih := ih (mgStep k st x)
      omega
    · have hne : a ≠ x := fun h => hxa h.symm
      rw [List.count_cons_of_ne hne]
      have hstep := mgStep_ge_other k st a x hxa
      have hih := ih (mgStep k st a)
      omega

/-- True frequency exceeds the counter by at most the number
of decrement rounds. -/
theorem freq_le_mg_add_rounds {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) (x : X) :
    s.count x ≤ (mgRun k s).1 x + (mgRun k s).2 := by
  have h := mgFold_ge k s (fun _ => 0, 0) x
  simpa [mgRun] using h

private theorem filter_update_of_pos {X : Type*} [DecidableEq X] [Fintype X]
    (c : X → ℕ) (a : X) (v : ℕ) (hpos : 0 < c a) (hv : 0 < v) :
    Finset.univ.filter (fun y => 0 < Function.update c a v y)
      = Finset.univ.filter (fun y => 0 < c y) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hya : y = a
  · subst hya
    rw [Function.update_self]
    exact iff_of_true hv hpos
  · have hu : Function.update c a v y = c y := Function.update_of_ne hya _ _
    rw [hu]

private theorem filter_update_insert {X : Type*} [DecidableEq X] [Fintype X]
    (c : X → ℕ) (a : X) (v : ℕ) (hv : 0 < v) :
    Finset.univ.filter (fun y => 0 < Function.update c a v y)
      = insert a (Finset.univ.filter (fun y => 0 < c y)) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hya : y = a
  · subst hya
    rw [Function.update_self]
    exact iff_of_true hv (Or.inl rfl)
  · have hu : Function.update c a v y = c y := Function.update_of_ne hya _ _
    rw [hu]
    simp [hya]

private theorem filter_decr_subset {X : Type*} [DecidableEq X] [Fintype X]
    (c : X → ℕ) :
    Finset.univ.filter (fun y => 0 < c y - 1)
      ⊆ Finset.univ.filter (fun y => 0 < c y) := by
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  omega

private theorem mgStep_card_le {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (a : X)
    (hle : (Finset.univ.filter (fun y => 0 < st.1 y)).card ≤ k - 1) :
    (Finset.univ.filter (fun y => 0 < (mgStep k st a).1 y)).card ≤ k - 1 := by
  unfold mgStep
  split_ifs with hc
  · by_cases hpos : 0 < st.1 a
    · have heq := filter_update_of_pos st.1 a (st.1 a + 1) hpos (by omega)
      show (Finset.univ.filter
        (fun y => 0 < Function.update st.1 a (st.1 a + 1) y)).card ≤ k - 1
      rw [heq]
      exact hle
    · have ha0 : st.1 a = 0 := by omega
      have hlt : (Finset.univ.filter (fun y => 0 < st.1 y)).card < k - 1 := by
        rcases hc with h | h
        · omega
        · exact h
      have heq := filter_update_insert st.1 a (st.1 a + 1) (by omega)
      show (Finset.univ.filter
        (fun y => 0 < Function.update st.1 a (st.1 a + 1) y)).card ≤ k - 1
      rw [heq]
      have hnotmem : a ∉ Finset.univ.filter (fun y => 0 < st.1 y) := by simp [ha0]
      rw [Finset.card_insert_of_notMem hnotmem]
      omega
  · show (Finset.univ.filter (fun y => 0 < st.1 y - 1)).card ≤ k - 1
    exact le_trans (Finset.card_le_card (filter_decr_subset st.1)) hle

private theorem mgFold_card_le {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) (st : (X → ℕ) × ℕ)
    (hle : (Finset.univ.filter (fun y => 0 < st.1 y)).card ≤ k - 1) :
    (Finset.univ.filter (fun y => 0 < (List.foldl (mgStep k) st s).1 y)).card
      ≤ k - 1 := by
  induction s generalizing st with
  | nil =>
    rw [List.foldl_nil]
    exact hle
  | cons a s ih =>
    rw [List.foldl_cons]
    exact ih _ (mgStep_card_le k st a hle)

private theorem sum_update_succ {X : Type*} [DecidableEq X] [Fintype X]
    (c : X → ℕ) (a : X) :
    ∑ y, Function.update c a (c a + 1) y = (∑ y, c y) + 1 := by
  have hmem : a ∈ Finset.univ := Finset.mem_univ a
  have e1 := Finset.add_sum_erase Finset.univ (Function.update c a (c a + 1)) hmem
  have e2 := Finset.add_sum_erase Finset.univ c hmem
  have hcongr : ∀ y ∈ Finset.univ.erase a, Function.update c a (c a + 1) y = c y := by
    intro y hy
    have hne : y ≠ a := (Finset.mem_erase.mp hy).1
    exact Function.update_of_ne hne _ _
  have hsum : ∑ y ∈ Finset.univ.erase a, Function.update c a (c a + 1) y
      = ∑ y ∈ Finset.univ.erase a, c y :=
    Finset.sum_congr rfl hcongr
  rw [hsum] at e1
  have hself : Function.update c a (c a + 1) a = c a + 1 :=
    Function.update_self _ _ _
  rw [hself] at e1
  omega

private theorem sum_decr_eq {X : Type*} [DecidableEq X] [Fintype X]
    (c : X → ℕ) :
    ∑ y, (c y - 1) = (∑ y, c y) - (Finset.univ.filter (fun y => 0 < c y)).card := by
  set S := Finset.univ.filter (fun y => 0 < c y) with hS
  have hsub : S ⊆ Finset.univ := Finset.filter_subset _ _
  have hzero1 : ∀ y ∈ Finset.univ, y ∉ S → c y - 1 = 0 := by
    intro y _ hy
    rw [hS] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hy
    omega
  have e1 := Finset.sum_subset hsub hzero1
  have h1 : ∀ y ∈ S, (c y - 1) + 1 = c y := by
    intro y hy
    rw [hS] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    omega
  have e2 : ∑ y ∈ S, ((c y - 1) + 1) = ∑ y ∈ S, c y := Finset.sum_congr rfl h1
  rw [Finset.sum_add_distrib] at e2
  have e3 : ∑ _y ∈ S, (1 : ℕ) = S.card := by simp
  rw [e3] at e2
  have hzero3 : ∀ y ∈ Finset.univ, y ∉ S → c y = 0 := by
    intro y _ hy
    rw [hS] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hy
    omega
  have e4 := Finset.sum_subset hsub hzero3
  omega

private theorem card_supp_le_sum {X : Type*} [DecidableEq X] [Fintype X]
    (c : X → ℕ) :
    (Finset.univ.filter (fun y => 0 < c y)).card ≤ ∑ y, c y := by
  have h1 : (Finset.univ.filter (fun y => 0 < c y)).card
      = ∑ _y ∈ Finset.univ.filter (fun y => 0 < c y), (1 : ℕ) := by simp
  have h2 : ∑ _y ∈ Finset.univ.filter (fun y => 0 < c y), (1 : ℕ)
      ≤ ∑ y ∈ Finset.univ.filter (fun y => 0 < c y), c y := by
    apply Finset.sum_le_sum
    intro y hy
    have hpos : 0 < c y := (Finset.mem_filter.mp hy).2
    show (1 : ℕ) ≤ c y
    omega
  have h3 : ∑ y ∈ Finset.univ.filter (fun y => 0 < c y), c y ≤ ∑ y, c y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun y _ _ => Nat.zero_le _)
  omega

private theorem mgStep_phi_le {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (st : (X → ℕ) × ℕ) (a : X)
    (hle : (Finset.univ.filter (fun y => 0 < st.1 y)).card ≤ k - 1) :
    (mgStep k st a).2 * (k - 1) + ∑ y, (mgStep k st a).1 y
      ≤ st.2 * (k - 1) + ∑ y, st.1 y + 1 := by
  unfold mgStep
  split_ifs with hc
  · have hsum := sum_update_succ st.1 a
    show st.2 * (k - 1) + ∑ y, Function.update st.1 a (st.1 a + 1) y
      ≤ st.2 * (k - 1) + ∑ y, st.1 y + 1
    rw [hsum]
    omega
  · have hnge : ¬ (Finset.univ.filter (fun y => 0 < st.1 y)).card < k - 1 :=
      fun h => hc (Or.inr h)
    have hcard : (Finset.univ.filter (fun y => 0 < st.1 y)).card = k - 1 :=
      le_antisymm hle (not_lt.mp hnge)
    have hsum : ∑ y, (st.1 y - 1) = (∑ y, st.1 y) - (k - 1) := by
      have h := sum_decr_eq st.1
      rw [hcard] at h
      exact h
    have hge : k - 1 ≤ ∑ y, st.1 y := by
      have h := card_supp_le_sum st.1
      rw [hcard] at h
      exact h
    show (st.2 + 1) * (k - 1) + ∑ y, (st.1 y - 1)
      ≤ st.2 * (k - 1) + ∑ y, st.1 y + 1
    rw [hsum]
    have hmul : (st.2 + 1) * (k - 1) = st.2 * (k - 1) + (k - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hmul]
    omega

private theorem mgFold_phi_le {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) (st : (X → ℕ) × ℕ)
    (hle : (Finset.univ.filter (fun y => 0 < st.1 y)).card ≤ k - 1) :
    (List.foldl (mgStep k) st s).2 * (k - 1)
        + ∑ y, (List.foldl (mgStep k) st s).1 y
      ≤ st.2 * (k - 1) + ∑ y, st.1 y + s.length := by
  induction s generalizing st with
  | nil =>
    rw [List.foldl_nil]
    have hlen : ([] : List X).length = 0 := rfl
    omega
  | cons a s ih =>
    rw [List.foldl_cons, List.length_cons]
    have hcard := mgStep_card_le k st a hle
    have hstep := mgStep_phi_le k st a hle
    have hih := ih _ hcard
    omega

private theorem mgRounds_bound {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (s : List X) :
    (mgRun k s).2 * (k - 1) ≤ s.length - ∑ y, (mgRun k s).1 y := by
  have hle : (Finset.univ.filter
      (fun y => 0 < ((fun _ => 0, 0) : (X → ℕ) × ℕ).1 y)).card ≤ k - 1 := by
    have h0 : (Finset.univ.filter
        (fun y => 0 < ((fun _ => 0, 0) : (X → ℕ) × ℕ).1 y)).card = 0 := by simp
    omega
  have hphi := mgFold_phi_le k s (fun _ => 0, 0) hle
  have hinit2 : ((fun _ => 0, 0) : (X → ℕ) × ℕ).2 = 0 := rfl
  have hinit1 : ∑ y, ((fun _ => 0, 0) : (X → ℕ) × ℕ).1 y = 0 := by simp
  rw [hinit2, hinit1] at hphi
  simp only [zero_mul, zero_add] at hphi
  unfold mgRun
  omega

/-- Deterministic Misra-Gries error bound: the frequency error
times `k - 1` is at most the stream mass not held in counters. -/
theorem mg_error_bound {X : Type*} [DecidableEq X] [Fintype X]
    (k : ℕ) (hk : 2 ≤ k) (s : List X) (x : X) :
    (s.count x - (mgRun k s).1 x) * (k - 1)
      ≤ s.length - ∑ y, (mgRun k s).1 y := by
  have h1 := mg_le_freq k s x
  have h2 := freq_le_mg_add_rounds k s x
  have h3 := mgRounds_bound k s
  have herr : s.count x - (mgRun k s).1 x ≤ (mgRun k s).2 := by omega
  have hmul := Nat.mul_le_mul_right (k - 1) herr
  exact le_trans hmul h3

end
