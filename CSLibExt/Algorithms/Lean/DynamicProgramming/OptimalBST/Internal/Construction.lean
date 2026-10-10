/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import all CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Basic

/-!
# Private optimal-BST construction facts

Source: CLRS, fourth edition, Section 14.5, pages 400-407 and Figure 14.10.
These private facts relate the actual ascending candidate loop to the earliest
strict-improvement root, saved interval weight, diagonal initialization, and frame.
They characterize the unchanged executor rather than a second optimizer.
-/

set_option autoImplicit false
universe u
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open scoped BigOperators
namespace Cslib.Algorithms.Lean.OptimalBST
variable {R : Type u}

private def scanPrefix [LinearOrder R] {n : Nat} (cost : Fin n → R)
    (first : Fin n) : (k : Nat) → first.val + k < n → Fin n
  | 0, _ => first
  | k + 1, h =>
      let previous := scanPrefix cost first k (by omega)
      let next : Fin n := ⟨first.val + k + 1, h⟩
      if cost next < cost previous then next else previous

private theorem scanPrefix_spec [LinearOrder R] {n : Nat} (cost : Fin n → R)
    (first : Fin n) (k : Nat) (h : first.val + k < n) :
    let chosen := scanPrefix cost first k h
    first.val ≤ chosen.val ∧ chosen.val ≤ first.val + k ∧
      ∀ t : Fin n, first.val ≤ t.val → t.val ≤ first.val + k →
        cost chosen ≤ cost t ∧ (t.val < chosen.val → cost chosen < cost t) := by
  induction k with
  | zero =>
    simp only [scanPrefix]
    constructor
    · exact Nat.le_refl _
    constructor
    · exact Nat.le_refl _
    intro t htLower htUpper
    have ht : t = first := Fin.ext (by omega)
    subst t
    exact ⟨le_rfl, fun hlt => (Nat.lt_irrefl _ hlt).elim⟩
  | succ k ih =>
    let previous := scanPrefix cost first k (by omega)
    let next : Fin n := ⟨first.val + k + 1, h⟩
    have hNextVal : next.val = first.val + k + 1 := rfl
    have hPrevious := ih (by omega)
    simp only [scanPrefix]
    split <;> rename_i hImproves
    · refine ⟨by omega, by omega, ?_⟩
      intro t htLower htUpper
      by_cases htNext : t.val = next.val
      · have ht : t = next := Fin.ext htNext
        subst t
        exact ⟨le_rfl, fun hlt => (Nat.lt_irrefl _ hlt).elim⟩
      · have htOld : t.val ≤ first.val + k := by omega
        have htBound := (hPrevious.2.2 t htLower htOld).1
        exact ⟨le_trans (le_of_lt hImproves) htBound,
          fun _ => lt_of_lt_of_le hImproves htBound⟩
    · refine ⟨hPrevious.1, by omega, ?_⟩
      intro t htLower htUpper
      by_cases htNext : t.val = next.val
      · have ht : t = next := Fin.ext htNext
        subst t
        exact ⟨le_of_not_gt hImproves, fun hlt => by
          have := hPrevious.2.1
          omega⟩
      · have htOld : t.val ≤ first.val + k := by omega
        exact hPrevious.2.2 t htLower htOld


private def rootLoop [LinearOrder R] {n : Nat}
    (cost : Fin n → R) (firstRoot : Fin n) (length : Nat)
    (hEnd : firstRoot.val + length ≤ n) (savedCount : Nat) :
    R × Fin n × Nat := Id.run do
    let firstCandidate := cost firstRoot
    let initialBest : WithTop R :=
      if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
    have finiteInitial : initialBest ≠ ⊤ := by
      simp [initialBest]
    let mut best := initialBest.untop finiteInitial
    let mut chosen := firstRoot
    let mut candidateCount := savedCount + 1
    for hr : rootOffset in [:length - 1] do
      have hRootOffset : rootOffset < length - 1 := hr.2.1
      let rootIndex := firstRoot.val + rootOffset + 1
      have hRoot : rootIndex < n := by omega
      let candidate := cost ⟨rootIndex, hRoot⟩
      if candidate < best then
        best := candidate
        chosen := ⟨rootIndex, hRoot⟩
      candidateCount := candidateCount + 1
    return (best, chosen, candidateCount)

private theorem yield_if {β : Type u} (p : Prop) [Decidable p] (a b : β) :
    (if p then (pure (.yield a) : Id (ForInStep β)) else pure (.yield b)) =
      pure (.yield (if p then a else b)) := by
  split <;> rfl

private theorem rootLoop_prefix [LinearOrder R] {n : Nat}
    (cost : Fin n → R) (firstRoot : Fin n) (k : Nat)
    (hEnd : firstRoot.val + k + 1 ≤ n) (savedCount : Nat) :
    let result : R × Fin n × Nat := Id.run do
      let mut best := cost firstRoot
      let mut chosen := firstRoot
      let mut candidateCount := savedCount + 1
      for hr : rootOffset in [:k] do
        have hRootOffset : rootOffset < k := hr.2.1
        let rootIndex := firstRoot.val + rootOffset + 1
        have hRoot : rootIndex < n := by omega
        let candidate := cost ⟨rootIndex, hRoot⟩
        if candidate < best then
          best := candidate
          chosen := ⟨rootIndex, hRoot⟩
        candidateCount := candidateCount + 1
      return (best, chosen, candidateCount)
    let chosen := scanPrefix cost firstRoot k (by omega)
    result = (cost chosen, chosen, savedCount + k + 1) := by
  induction k with
  | zero =>
    simp [scanPrefix]
  | succ k ih =>
    have ih' := ih (by omega)
    simp [Std.Legacy.Range.forIn'_eq_forIn'_range', yield_if, Nat.add_assoc] at ih'
    simp [Std.Legacy.Range.forIn'_eq_forIn'_range', List.range'_1_concat,
      yield_if, List.foldl_map, ih', scanPrefix, Nat.add_assoc]
    split <;> rfl

set_option backward.proofsInPublic true in
/-- Private correspondence for the actual ascending strict-improvement root scan.
The callback is the frozen saved-child candidate expression, not another optimizer. -/
private theorem rootLoop_ret_time [LinearOrder R] {n : Nat}
    (cost : Fin n → R) (firstRoot : Fin n) (length : Nat)
    (hLength : 0 < length) (hEnd : firstRoot.val + length ≤ n)
    (savedCount : Nat) :
    let result := rootLoop cost firstRoot length hEnd savedCount
    result.1 = cost result.2.1 ∧
      result.2.1 = scanPrefix cost firstRoot (length - 1) (by omega) ∧
      result.2.2 = savedCount + length := by
  have hPrefix := rootLoop_prefix cost firstRoot (length - 1) (by omega) savedCount
  have hRootLoop :
      rootLoop cost firstRoot length hEnd savedCount =
        let chosen := scanPrefix cost firstRoot (length - 1) (by omega)
        (cost chosen, chosen, savedCount + (length - 1) + 1) := by
    simpa [rootLoop] using hPrefix
  dsimp only
  rw [hRootLoop]
  refine ⟨rfl, rfl, ?_⟩
  dsimp only
  omega


private theorem diagonal_prefix {n : Nat} (q : Vector R (n + 1))
    (e₀ w₀ : Vector (Vector R (n + 1)) (n + 1))
    (m : Nat) (hm : m ≤ n + 1) :
    let result := Id.run do
      let mut e := e₀
      let mut w := w₀
      for hi : i in [:m] do
        have hiM : i < m := hi.2.1
        have hiN : i < n + 1 := by omega
        e := e.set i (e[i].set i q[i])
        w := w.set i (w[i].set i q[i])
      return (e, w)
    (∀ i j : Fin (n + 1), result.1[i.val][j.val] =
      if i = j ∧ i.val < m then q[i.val] else e₀[i.val][j.val]) ∧
    (∀ i j : Fin (n + 1), result.2[i.val][j.val] =
      if i = j ∧ i.val < m then q[i.val] else w₀[i.val][j.val]) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (by omega)
    simp [Std.Legacy.Range.forIn'_eq_forIn'_range'] at ih'
    simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      tsub_zero, add_tsub_cancel_right, Nat.div_one, List.range'_1_concat, zero_add,
      List.forIn'_pure_yield_eq_foldl, List.attach_append, List.attach_cons,
      List.attach_nil, List.map_nil, List.map_cons, List.foldl_append, List.foldl_map,
      List.foldl_cons, List.foldl_nil, Prod.mk.eta, bind_pure, Id.run_pure]
    constructor <;> intro i j
    · by_cases him : m = i.val
      · by_cases hjm : m = j.val
        · have hij : i = j := Fin.ext (by omega)
          simp [him, hij]
        · have hij : i ≠ j := by intro h; have := congrArg Fin.val h; omega
          have hijVal : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simpa [Vector.getElem_set, him, hij, hijVal] using ih'.1 i j
      · have hs : (i = j ∧ i.val < m + 1) ↔ (i = j ∧ i.val < m) := by omega
        simpa [Vector.getElem_set, him, hs] using ih'.1 i j
    · by_cases him : m = i.val
      · by_cases hjm : m = j.val
        · have hij : i = j := Fin.ext (by omega)
          simp [him, hij]
        · have hij : i ≠ j := by intro h; have := congrArg Fin.val h; omega
          have hijVal : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simpa [Vector.getElem_set, him, hij, hijVal] using ih'.2 i j
      · have hs : (i = j ∧ i.val < m + 1) ↔ (i = j ∧ i.val < m) := by omega
        simpa [Vector.getElem_set, him, hs] using ih'.2 i j


private theorem interval_write [AddCommMonoid R] [LinearOrder R]
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
    result =
      (e₀.set a (e₀[a].set b (cost chosen)),
        w₀.set a (w₀[a].set b savedWeight),
        roots₀.set a (roots₀[a].set (b - 1) (some chosen)),
        savedCount + length) := by
  dsimp only
  have aBound : a < n + 1 := by omega
  have bBound : a + length < n + 1 := by omega
  have rootRowBound : a < n := by omega
  have rootColumnBound : a + length - 1 < n := by omega
  let b := a + length
  let savedWeight := w₀[a][b - 1] + p[b - 1] + q[b]
  let cost (r : Fin n) : R :=
    e₀[a][r.val] + e₀[r.val + 1][b] + savedWeight
  let firstRoot : Fin n := ⟨a, by omega⟩
  let chosen := scanPrefix cost firstRoot (length - 1) (by dsimp [firstRoot]; omega)
  have hRootEnd : firstRoot.val + length ≤ n := by dsimp [firstRoot]; exact hEnd
  have hScan : rootLoop cost firstRoot length hRootEnd savedCount =
      (cost chosen, chosen, savedCount + length) := by
    have h := rootLoop_ret_time cost firstRoot length hLength hRootEnd savedCount
    dsimp only at h
    apply Prod.ext
    · rw [h.1, h.2.1]
    · exact Prod.ext h.2.1 h.2.2
  let index (x : {i : Nat // i ∈ List.range' 0 (length - 1)}) : Fin n :=
    ⟨a + x.val + 1, by have hx := List.mem_range'.mp x.property; omega⟩
  let step₁ (s : Nat × R × Fin n)
      (x : {i : Nat // i ∈ List.range' 0 (length - 1)}) : Nat × R × Fin n :=
    if cost (index x) < s.2.1 then (s.1 + 1, cost (index x), index x)
    else (s.1 + 1, s.2.1, s.2.2)
  let step₂ (s : R × Fin n × Nat)
      (x : {i : Nat // i ∈ List.range' 0 (length - 1)}) : R × Fin n × Nat :=
    if cost (index x) < s.1 then (cost (index x), index x, s.2.2 + 1)
    else (s.1, s.2.1, s.2.2 + 1)
  have hHom := List.foldl_hom
    (fun s : Nat × R × Fin n => (s.2.1, s.2.2, s.1))
    (g₁ := step₁) (g₂ := step₂)
    (l := (List.range' 0 (length - 1)).attach)
    (init := (savedCount + 1, cost firstRoot, firstRoot)) (by
      intro s x
      dsimp [step₁, step₂]
      split <;> rfl)
  have hSecond :
      (List.range' 0 (length - 1)).attach.foldl step₂
        (cost firstRoot, firstRoot, savedCount + 1) =
      (cost chosen, chosen, savedCount + length) := by
    simpa [rootLoop, Std.Legacy.Range.forIn'_eq_forIn'_range',
      yield_if, step₂, index] using hScan
  have hFirst := hHom.symm.trans hSecond
  have hBest := congrArg (fun s => s.1) hFirst
  have hChosen := congrArg (fun s => s.2.1) hFirst
  have hCount := congrArg (fun s => s.2.2) hFirst
  have hState :
      (List.range' 0 (length - 1)).attach.foldl step₁
        (savedCount + 1, cost firstRoot, firstRoot) =
      (savedCount + length, cost chosen, chosen) :=
    Prod.ext hCount (Prod.ext hBest hChosen)
  have hWrites := congrArg (fun s : Nat × R × Fin n =>
      (e₀.set a ((e₀[a]'aBound).set b s.2.1 bBound) aBound,
        w₀.set a ((w₀[a]'aBound).set b savedWeight bBound) aBound,
        roots₀.set a ((roots₀[a]'rootRowBound).set (b - 1) (some s.2.2)
          rootColumnBound) rootRowBound, s.1)) hState
  simp only [Prod.mk.eta, Prod.mk.injEq, true_and, WithTop.coe_add,
    WithTop.add_lt_top, WithTop.coe_lt_top, and_self, ↓reduceIte, yield_if,
    Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size, tsub_zero,
    add_tsub_cancel_right, Nat.div_one, List.forIn'_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, Id.run_pure, b, step₁, cost, savedWeight, index,
    firstRoot, chosen] at hWrites ⊢
  exact hWrites


private theorem cell_frame_shorter {n : Nat}
    (table : Vector (Vector R (n + 1)) (n + 1))
    (a b i j : Fin (n + 1)) (value : R)
    (hShorter : j.val - i.val < b.val - a.val) :
    (table.set a.val (table[a.val].set b.val value))[i.val][j.val] =
      table[i.val][j.val] := by
  by_cases ha : a.val = i.val
  · have hi : i = a := Fin.ext ha.symm
    subst i
    have hj : b.val ≠ j.val := by omega
    simp [hj]
  · simp [ha]

private theorem cell_frame_other_start {n : Nat}
    (table : Vector (Vector R (n + 1)) (n + 1))
    (a b i j : Fin (n + 1)) (value : R) (hStart : i ≠ a) :
    (table.set a.val (table[a.val].set b.val value))[i.val][j.val] =
      table[i.val][j.val] := by
  have ha : a.val ≠ i.val := fun h => hStart (Fin.ext h.symm)
  simp [ha]


private def intervalMass [AddCommMonoid R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1)) (a b : Nat) : R :=
  (∑ i : Fin n, if a ≤ i.val ∧ i.val < b then p[i.val] else 0) +
    ∑ i : Fin (n + 1), if a ≤ i.val ∧ i.val ≤ b then q[i.val] else 0

private theorem fin_sum_interval_last [AddCommMonoid R] {N : Nat}
    (f : Fin N → R) (a : Nat) (b : Fin N) (hab : a ≤ b.val) :
    (∑ i : Fin N, if a ≤ i.val ∧ i.val ≤ b.val then f i else 0) =
      (∑ i : Fin N, if a ≤ i.val ∧ i.val < b.val then f i else 0) + f b := by
  have hSingle : f b = ∑ i : Fin N, if i = b then f i else 0 := by
    symm
    exact (Finset.sum_eq_single_of_mem (f := fun i => if i = b then f i else 0)
      b (Finset.mem_univ _) (by intro i _ hi; exact ite_eq_right hi)).trans
        (ite_eq_left rfl)
  rw [hSingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = b
  · subst i
    rw [ite_eq_left ⟨hab, le_rfl⟩, ite_eq_right (by omega), ite_eq_left rfl, zero_add]
  · have hiVal : i.val ≠ b.val := fun h => hi (Fin.ext h)
    by_cases hOld : a ≤ i.val ∧ i.val < b.val
    · have hNew : a ≤ i.val ∧ i.val ≤ b.val := by omega
      simp only [ite_eq_right hi, ite_eq_left hOld, ite_eq_left hNew, add_zero]
    · have hNew : ¬(a ≤ i.val ∧ i.val ≤ b.val) := by omega
      simp only [ite_eq_right hi, ite_eq_right hOld, ite_eq_right hNew, add_zero]

private theorem intervalMass_diagonal [AddCommMonoid R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1)) (a : Fin (n + 1)) :
    intervalMass p q a.val a.val = q[a.val] := by
  have hEmpty : ∀ i : Fin n, ¬(a.val ≤ i.val ∧ i.val < a.val) := by
    intro i
    omega
  have hPoint : ∀ i : Fin (n + 1),
      (a.val ≤ i.val ∧ i.val ≤ a.val) ↔ i = a := by
    intro i
    constructor
    · intro h
      exact Fin.ext (by omega)
    · intro h
      subst i
      exact ⟨le_rfl, le_rfl⟩
  simp only [intervalMass, hEmpty, hPoint, ite_false, Finset.sum_const_zero, zero_add]
  exact (Finset.sum_eq_single_of_mem (f := fun i => if i = a then q[i.val] else 0)
    a (Finset.mem_univ _) (by intro i _ hi; exact ite_eq_right hi)).trans
      (ite_eq_left rfl)

private theorem intervalMass_step [AddCommMonoid R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1)) (a b : Nat)
    (hab : a < b) (hb : b ≤ n) :
    intervalMass p q a b = intervalMass p q a (b - 1) + p[b - 1] + q[b] := by
  have hKey := fin_sum_interval_last (fun i : Fin n => p[i.val]) a
    (⟨b - 1, by omega⟩ : Fin n) (by dsimp only; omega)
  have hDummy := fin_sum_interval_last (fun i : Fin (n + 1) => q[i.val]) a
    (⟨b, by omega⟩ : Fin (n + 1)) (by dsimp only; omega)
  have hKeyEnd : ∀ i : Fin n, (a ≤ i.val ∧ i.val ≤ b - 1) ↔
      (a ≤ i.val ∧ i.val < b) := by intro i; omega
  have hDummyEnd : ∀ i : Fin (n + 1), (a ≤ i.val ∧ i.val < b) ↔
      (a ≤ i.val ∧ i.val ≤ b - 1) := by intro i; omega
  simp only [hKeyEnd] at hKey
  simp only [hDummyEnd] at hDummy
  dsimp only [intervalMass]
  rw [hKey, hDummy]
  ac_rfl


private def CellSpec [AddCommMonoid R] [LinearOrder R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (e : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (a : Fin n) (b : Fin (n + 1)) (hab : a.val < b.val) : Prop :=
  ∃ r : Fin n, a.val ≤ r.val ∧ r.val < b.val ∧
    root[a.val][b.val - 1]'(by omega) = some r ∧
    e[a.val][b.val] = e[a.val][r.val] + e[r.val + 1][b.val] +
      intervalMass p q a.val b.val ∧
    ∀ t : Fin n, a.val ≤ t.val → t.val < b.val →
      e[a.val][b.val] ≤ e[a.val][t.val] + e[t.val + 1][b.val] +
        intervalMass p q a.val b.val ∧
      (t.val < r.val → e[a.val][b.val] <
        e[a.val][t.val] + e[t.val + 1][b.val] + intervalMass p q a.val b.val)

private theorem cell_selected_spec [AddCommMonoid R] [LinearOrder R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (e : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (a : Fin n) (b : Fin (n + 1)) (hab : a.val < b.val) :
    let cost (r : Fin n) :=
      e[a.val][r.val] + e[r.val + 1][b.val] + intervalMass p q a.val b.val
    let chosen := scanPrefix cost a (b.val - a.val - 1) (by omega)
    CellSpec p q (e.set a.val (e[a.val].set b.val (cost chosen)))
      (root.set a.val (root[a.val].set (b.val - 1) (some chosen) (by omega)))
      a b hab := by
  dsimp only
  let cost (r : Fin n) :=
    e[a.val][r.val] + e[r.val + 1][b.val] + intervalMass p q a.val b.val
  let chosen := scanPrefix cost a (b.val - a.val - 1) (by omega)
  let e' := e.set a.val (e[a.val].set b.val (cost chosen))
  let root' := root.set a.val (root[a.val].set (b.val - 1) (some chosen) (by omega))
  change CellSpec p q e' root' a b hab
  have hChosen := scanPrefix_spec cost a (b.val - a.val - 1) (by omega)
  have hLower : a.val ≤ chosen.val := hChosen.1
  have hUpper : chosen.val < b.val := by
    have := hChosen.2.1
    omega
  have hFrame : ∀ r : Fin n, a.val ≤ r.val → r.val < b.val →
      e'[a.val][r.val] = e[a.val][r.val] ∧
      e'[r.val + 1][b.val] = e[r.val + 1][b.val] := by
    intro r hLower hUpper
    constructor
    · exact cell_frame_shorter e a.castSucc b a.castSucc r.castSucc
        (cost chosen) (by change r.val - a.val < b.val - a.val; omega)
    · exact cell_frame_shorter e a.castSucc b
        ⟨r.val + 1, by omega⟩ b (cost chosen)
        (by change b.val - (r.val + 1) < b.val - a.val; omega)
  have hValue : e'[a.val][b.val] = cost chosen := by simp [e']
  refine ⟨chosen, hLower, hUpper, ?_, ?_, ?_⟩
  · simp [root']
  · rw [hValue, (hFrame chosen hLower hUpper).1,
      (hFrame chosen hLower hUpper).2]
  · intro t htLower htUpper
    rw [hValue, (hFrame t htLower htUpper).1, (hFrame t htLower htUpper).2]
    exact hChosen.2.2 t htLower (by omega)


private theorem cellSpec_prior [AddCommMonoid R] [LinearOrder R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (e : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (a i : Fin n) (b j : Fin (n + 1))
    (hab : a.val < b.val) (hij : i.val < j.val)
    (value : R) (selected : Fin n)
    (hWidth : j.val - i.val ≤ b.val - a.val)
    (hPrior : j.val - i.val < b.val - a.val ∨ i ≠ a)
    (hSpec : CellSpec p q e root i j hij) :
    CellSpec p q (e.set a.val (e[a.val].set b.val value))
      (root.set a.val (root[a.val].set (b.val - 1) (some selected) (by omega)))
      i j hij := by
  let e' := e.set a.val (e[a.val].set b.val value)
  let root' := root.set a.val (root[a.val].set (b.val - 1) (some selected) (by omega))
  change CellSpec p q e' root' i j hij
  have hValue : e'[i.val][j.val] = e[i.val][j.val] := by
    rcases hPrior with hShorter | hOther
    · exact cell_frame_shorter e a.castSucc b i.castSucc j value
        (by change j.val - i.val < b.val - a.val; exact hShorter)
    · exact cell_frame_other_start e a.castSucc b i.castSucc j value
        (by
          intro h
          exact hOther (Fin.ext (congrArg (fun x : Fin (n + 1) => x.val) h)))
  have hRoot : root'[i.val][j.val - 1]'(by omega) =
      root[i.val][j.val - 1]'(by omega) := by
    by_cases ha : a.val = i.val
    · have hi : i = a := Fin.ext ha.symm
      subst i
      have hEnd : b.val - 1 ≠ j.val - 1 := by
        rcases hPrior with hShorter | hOther
        · omega
        · exact (hOther rfl).elim
      simp [root', hEnd]
    · simp [root', ha]
  have hChildren : ∀ r : Fin n, i.val ≤ r.val → r.val < j.val →
      e'[i.val][r.val] = e[i.val][r.val] ∧
      e'[r.val + 1][j.val] = e[r.val + 1][j.val] := by
    intro r hLower hUpper
    constructor
    · exact cell_frame_shorter e a.castSucc b i.castSucc r.castSucc value
        (by change r.val - i.val < b.val - a.val; omega)
    · exact cell_frame_shorter e a.castSucc b ⟨r.val + 1, by omega⟩ j value
        (by change j.val - (r.val + 1) < b.val - a.val; omega)
  rcases hSpec with ⟨r, hLower, hUpper, hSaved, hRecurrence, hMinimum⟩
  refine ⟨r, hLower, hUpper, ?_, ?_, ?_⟩
  · rw [hRoot]
    exact hSaved
  · rw [hValue, (hChildren r hLower hUpper).1, (hChildren r hLower hUpper).2]
    exact hRecurrence
  · intro t htLower htUpper
    rw [hValue, (hChildren t htLower htUpper).1, (hChildren t htLower htUpper).2]
    exact hMinimum t htLower htUpper


private def Settled [AddCommMonoid R] [LinearOrder R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (e w : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (length start : Nat) : Prop :=
  (∀ i : Fin (n + 1), e[i.val][i.val] = q[i.val]) ∧
    (∀ a b : Fin (n + 1), a.val ≤ b.val →
      (b.val - a.val < length ∨ b.val - a.val = length ∧ a.val < start) →
      w[a.val][b.val] = intervalMass p q a.val b.val) ∧
    (∀ (a : Fin n) (b : Fin (n + 1)) (hab : a.val < b.val),
      (b.val - a.val < length ∨ b.val - a.val = length ∧ a.val < start) →
      CellSpec p q e root a b hab)

private theorem settled_of_diagonals [AddCommMonoid R] [LinearOrder R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (e w : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (hE : ∀ i : Fin (n + 1), e[i.val][i.val] = q[i.val])
    (hW : ∀ i : Fin (n + 1), w[i.val][i.val] = q[i.val]) :
    Settled p q e w root 1 0 := by
  refine ⟨hE, ?_, ?_⟩
  · intro a b hab hProcessed
    have hab' : a = b := Fin.ext (by omega)
    subst b
    rw [hW, intervalMass_diagonal]
  · intro a b hab hProcessed
    omega

private theorem settled_next_length [AddCommMonoid R] [LinearOrder R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (e w : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n) (length : Nat)
    (hSettled : Settled p q e w root length (n - length + 1)) :
    Settled p q e w root (length + 1) 0 := by
  refine ⟨hSettled.1, ?_, ?_⟩
  · intro a b hab hProcessed
    apply hSettled.2.1 a b hab
    by_cases hShorter : b.val - a.val < length
    · exact Or.inl hShorter
    · exact Or.inr ⟨by omega, by omega⟩
  · intro a b hab hProcessed
    apply hSettled.2.2 a b hab
    by_cases hShorter : b.val - a.val < length
    · exact Or.inl hShorter
    · exact Or.inr ⟨by omega, by omega⟩

end Cslib.Algorithms.Lean.OptimalBST
