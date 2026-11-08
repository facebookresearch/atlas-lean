/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Correctness
import all CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Internal.Construction
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimal-BST candidate-event cost

Source: CLRS, fourth edition, Section 14.5, pages 400-407 and Figure 14.10.
Time counts the candidate evaluations performed by the same saved-table executor,
including each interval's first candidate. The exact count is `choose (n+2) 3`;
the bounds concern this selected event metric only. Full RAM, word, bit, allocator,
and space costs are excluded and remain separate source-resource obligations.
-/

set_option autoImplicit false
universe u
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open scoped BigOperators
namespace Cslib.Algorithms.Lean.OptimalBST
variable {R : Type u}

universe v w

private theorem fold_count {α : Type v} {β : Type w}
    (step : β → α → β) (count : β → Nat) (charge : α → Nat)
    (hStep : ∀ state item, count (step state item) = count state + charge item)
    (items : List α) (initial : β) :
    count (items.foldl step initial) = count initial + (items.map charge).sum := by
  have h := List.foldl_hom count (g₁ := step)
    (g₂ := fun saved item => saved + charge item) (l := items)
    (init := initial) (fun state item => (hStep state item).symm)
  rw [← h, ← List.foldl_map, List.sum_eq_foldl]
  simpa only [Nat.add_zero] using
    (List.foldl_assoc (op := fun a b : Nat => a + b) (l := items.map charge)
      (a₁ := count initial) (a₂ := 0))

private theorem interval_write_count [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e₀ w₀ : Vector (Vector R (n + 1)) (n + 1))
    (roots₀ : Vector (Vector (Option (Fin n)) n) n)
    (a length : Nat) (hLength : 0 < length) (hEnd : a + length ≤ n)
    (savedCount : Nat) :
    have hA : a < n := by omega
    let b := a + length
    have hB : b ≤ n := by omega
    let savedWeight := w₀[a][b - 1] + p[b - 1] + q[b]
    let cost (r : Fin n) : R :=
      e₀[a][r.val] + e₀[r.val + 1][b] + savedWeight
    let firstRoot : Fin n := ⟨a, hA⟩
    let chosen := scanPrefix cost firstRoot (length - 1) (by dsimp [firstRoot]; omega)
    let result : Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector (Option (Fin n)) n) n × Nat := Id.run do
      let mut e := e₀
      let mut w := w₀
      let mut root := roots₀
      let mut candidateCount := savedCount
      w := w.set a (w[a].set b savedWeight)
      let firstCandidate := e[a][a] + e[a + 1][b] + savedWeight
      let initialBest : WithTop R :=
        if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
      have finiteInitial : initialBest ≠ ⊤ := by
        simp [initialBest]
      let mut best := initialBest.untop finiteInitial
      let mut selected := firstRoot
      candidateCount := candidateCount + 1
      for hr : rootOffset in [:length - 1] do
        have hRootOffset : rootOffset < length - 1 := hr.2.1
        let rootIndex := a + rootOffset + 1
        have hRoot : rootIndex < n := by omega
        have hLeft : rootIndex < n + 1 := by omega
        have hRight : rootIndex + 1 < n + 1 := by omega
        let candidate := e[a][rootIndex] + e[rootIndex + 1][b] + savedWeight
        if candidate < best then
          best := candidate
          selected := ⟨rootIndex, hRoot⟩
        candidateCount := candidateCount + 1
      e := e.set a (e[a].set b best)
      root := root.set a (root[a].set (b - 1) (some selected))
      return (e, w, root, candidateCount)
    result.2.2.2 = savedCount + length := by
  dsimp only
  have hWrite := interval_write p q e₀ w₀ roots₀ a length hLength hEnd savedCount
  dsimp only at hWrite
  exact congrArg (fun state => state.2.2.2) hWrite

private theorem interval_starts_count [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e₀ w₀ : Vector (Vector R (n + 1)) (n + 1))
    (roots₀ : Vector (Vector (Option (Fin n)) n) n)
    (length : Nat) (hLength : 0 < length) (hLengthN : length ≤ n)
    (m : Nat) (hm : m ≤ n - length + 1) (savedCount : Nat) :
    let result := Id.run do
      let mut e := e₀
      let mut w := w₀
      let mut root := roots₀
      let mut candidateCount := savedCount
      for ha : a in [:m] do
        have hStart : a < n - length + 1 := by
          have h : a < m := ha.2.1
          omega
        let b := a + length
        have hB : b ≤ n := by omega
        have hA : a < n := by omega
        let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
        w := w.set a (w[a].set b savedWeight)
        let firstRoot : Fin n := ⟨a, hA⟩
        let firstCandidate := e[a][a] + e[a + 1][b] + savedWeight
        let initialBest : WithTop R :=
          if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
        have finiteInitial : initialBest ≠ ⊤ := by
          simp [initialBest]
        let mut best := initialBest.untop finiteInitial
        let mut chosen := firstRoot
        candidateCount := candidateCount + 1
        for hr : rootOffset in [:length - 1] do
          have hRootOffset : rootOffset < length - 1 := hr.2.1
          let rootIndex := a + rootOffset + 1
          have hRoot : rootIndex < n := by omega
          have hLeft : rootIndex < n + 1 := by omega
          have hRight : rootIndex + 1 < n + 1 := by omega
          let candidate := e[a][rootIndex] + e[rootIndex + 1][b] + savedWeight
          if candidate < best then
            best := candidate
            chosen := ⟨rootIndex, hRoot⟩
          candidateCount := candidateCount + 1
        e := e.set a (e[a].set b best)
        root := root.set a (root[a].set (b - 1) (some chosen))
      return (e, w, root, candidateCount)
    result.2.2.2 = savedCount + length * m := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
    List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  refine (fold_count _ (fun state :
      Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector (Option (Fin n)) n) n × Nat => state.2.2.2)
    (fun _ : {a : Nat // a ∈ List.range' 0 m} => length) ?_
    (List.range' 0 m).attach (e₀, w₀, roots₀, savedCount)).trans ?_
  · intro state item
    have hItem := List.mem_range'.mp item.property
    have hStep := interval_write_count p q state.1 state.2.1 state.2.2.1
      item.val length hLength (by omega) state.2.2.2
    simpa only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
      List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure] using hStep
  · simp [Nat.mul_comm]

private theorem interval_lengths_count [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e₀ w₀ : Vector (Vector R (n + 1)) (n + 1))
    (roots₀ : Vector (Vector (Option (Fin n)) n) n)
    (k : Nat) (hk : k ≤ n) (savedCount : Nat) :
    let result := Id.run do
      let mut e := e₀
      let mut w := w₀
      let mut root := roots₀
      let mut candidateCount := savedCount
      for hl : lengthOffset in [:k] do
        have hLengthOffset : lengthOffset < n := by
          have h : lengthOffset < k := hl.2.1
          omega
        let length := lengthOffset + 1
        for ha : a in [:n - length + 1] do
          have hStart : a < n - length + 1 := ha.2.1
          let b := a + length
          have hB : b ≤ n := by omega
          have hA : a < n := by omega
          let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
          w := w.set a (w[a].set b savedWeight)
          let firstRoot : Fin n := ⟨a, hA⟩
          let firstCandidate := e[a][a] + e[a + 1][b] + savedWeight
          let initialBest : WithTop R :=
            if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
          have finiteInitial : initialBest ≠ ⊤ := by
            simp [initialBest]
          let mut best := initialBest.untop finiteInitial
          let mut chosen := firstRoot
          candidateCount := candidateCount + 1
          for hr : rootOffset in [:length - 1] do
            have hRootOffset : rootOffset < length - 1 := hr.2.1
            let rootIndex := a + rootOffset + 1
            have hRoot : rootIndex < n := by omega
            have hLeft : rootIndex < n + 1 := by omega
            have hRight : rootIndex + 1 < n + 1 := by omega
            let candidate := e[a][rootIndex] + e[rootIndex + 1][b] + savedWeight
            if candidate < best then
              best := candidate
              chosen := ⟨rootIndex, hRoot⟩
            candidateCount := candidateCount + 1
          e := e.set a (e[a].set b best)
          root := root.set a (root[a].set (b - 1) (some chosen))
      return (e, w, root, candidateCount)
    result.2.2.2 = savedCount +
      ((List.range' 0 k).attach.map (fun i => (i.val + 1) * (n - i.val))).sum := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
    List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  refine fold_count _ (fun state :
      Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector (Option (Fin n)) n) n × Nat => state.2.2.2)
    (fun i : {i : Nat // i ∈ List.range' 0 k} => (i.val + 1) * (n - i.val))
    ?_ (List.range' 0 k).attach (e₀, w₀, roots₀, savedCount)
  intro state item
  have hItem := List.mem_range'.mp item.property
  have hCount := interval_starts_count p q state.1 state.2.1 state.2.2.1
    (item.val + 1) (by omega) (by omega)
    (n - (item.val + 1) + 1) (le_rfl) state.2.2.2
  have hStarts : n - (item.val + 1) + 1 = n - item.val := by omega
  simp only [hStarts] at hCount
  simpa only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
    List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure] using hCount

private theorem execute_count_sum [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) :
    (execute p q).2.2.2 =
      ((List.range' 0 n).attach.map (fun i => (i.val + 1) * (n - i.val))).sum := by
  let initialized := Id.run do
    let mut e := Vector.replicate (n + 1) (Vector.replicate (n + 1) (0 : R))
    let mut w := Vector.replicate (n + 1) (Vector.replicate (n + 1) (0 : R))
    for hi : i in [:n + 1] do
      e := e.set i (e[i].set i q[i])
      w := w.set i (w[i].set i q[i])
    return (e, w)
  have hCount := interval_lengths_count p q initialized.1 initialized.2
    (Vector.replicate n (Vector.replicate n (none : Option (Fin n)))) n le_rfl 0
  simpa only [execute, initialized, Std.Legacy.Range.forIn'_eq_forIn'_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    yield_if, List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure,
    Nat.zero_add] using hCount


private theorem offset_sum_choose_two (n : Nat) :
    ((List.range n).map (fun k => k + 1)).sum = (n + 1).choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.sum_range_succ, ih]
    rw [show n + 1 + 1 = (n + 1).succ from rfl,
      Nat.choose_succ_succ (n + 1) 1]
    simp only [Nat.choose_one_right]
    exact Nat.add_comm _ _

private theorem candidate_sum_choose_three (n : Nat) :
    ((List.range n).map (fun k => (k + 1) * (n - k))).sum = (n + 2).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.sum_range_succ]
    have hMap : (List.range n).map (fun k => (k + 1) * (n + 1 - k)) =
        (List.range n).map (fun k => (k + 1) * (n - k) + (k + 1)) := by
      apply List.map_congr_left
      intro k hk
      have hkN : k < n := List.mem_range.mp hk
      rw [show n + 1 - k = n - k + 1 from by omega, Nat.mul_add, Nat.mul_one]
    rw [hMap, List.sum_map_add, ih, offset_sum_choose_two]
    simp only [Nat.add_sub_cancel_left, Nat.mul_one]
    have hTwo : (n + 1).choose 2 + (n + 1) = (n + 2).choose 2 := by
      rw [show n + 2 = (n + 1).succ from by omega,
        Nat.choose_succ_succ (n + 1) 1]
      simp only [Nat.choose_one_right]
      exact Nat.add_comm _ _
    rw [Nat.add_assoc, hTwo]
    rw [show n + 1 + 2 = (n + 2).succ from by omega,
      Nat.choose_succ_succ (n + 2) 2]
    exact Nat.add_comm _ _

private theorem execute_count_choose [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) :
    (execute p q).2.2.2 = (n + 2).choose 3 := by
  rw [execute_count_sum]
  have hMap : (List.range' 0 n).attach.map
      (fun i => (i.val + 1) * (n - i.val)) =
      (List.range n).map (fun k => (k + 1) * (n - k)) := by
    rw [show (fun i : {i // i ∈ List.range' 0 n} => (i.val + 1) * (n - i.val)) =
      (fun k => (k + 1) * (n - k)) ∘ Subtype.val from rfl]
    rw [← List.map_map, List.attach_map_subtype_val, ← List.range_eq_range']
  rw [hMap]
  exact candidate_sum_choose_three n


/-- The coupled execution charges exactly one tick for each candidate. -/
public theorem optimalBST_time [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] :
    ∀ (n : Nat) (p : Vector R n) (q : Vector R (n + 1)),
      (optimalBST p q).time = Nat.choose (n + 2) 3 := by
  intro n p q
  exact execute_count_choose p q

private theorem six_mul_choose_three (n : Nat) :
    6 * Nat.choose (n + 2) 3 = n * (n + 1) * (n + 2) := by
  calc
    6 * Nat.choose (n + 2) 3 = (n + 2).descFactorial 3 := by
      simpa [Nat.factorial] using (Nat.descFactorial_eq_factorial_mul_choose (n + 2) 3).symm
    _ = n * (n + 1) * (n + 2) := by
      simp [Nat.descFactorial, show n + 2 - 1 = n + 1 by omega, Nat.mul_assoc]

/-- Cubic lower and upper bounds for the selected candidate-event metric. -/
public theorem optimalBST_time_bounds [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] :
    ∀ (n : Nat) (p : Vector R n) (q : Vector R (n + 1)),
      n ^ 3 ≤ 6 * (optimalBST p q).time ∧ (optimalBST p q).time ≤ n ^ 3 := by
  intro n p q
  rw [optimalBST_time]
  constructor
  · rw [six_mul_choose_three]
    nlinarith [Nat.zero_le n]
  · have identity := six_mul_choose_three n
    by_cases small : n = 0
    · subst n
      decide
    · have positive : 0 < n := Nat.pos_of_ne_zero small
      have first : n + 1 ≤ 2 * n := by omega
      have second : n + 2 ≤ 3 * n := by omega
      have productBound : n * (n + 1) * (n + 2) ≤ 6 * n ^ 3 := by
        calc
          _ ≤ n * (2 * n) * (3 * n) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left n first) second
          _ = 6 * n ^ 3 := by ring
      nlinarith [productBound]

end Cslib.Algorithms.Lean.OptimalBST
