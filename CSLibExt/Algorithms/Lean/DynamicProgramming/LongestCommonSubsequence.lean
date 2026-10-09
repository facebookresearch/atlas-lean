/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

/-!
# Longest common subsequence

Bottom-up prefix dynamic programming and witness reconstruction following CLRS, fourth edition,
section 14.4, pages 393-399. The abstract cost counts one tick per interior table transition and
one per nonterminal reconstruction transition. Initialization, allocation, access, comparison,
arithmetic, and list construction are free in this model.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

universe u

open List

private def CellOptimal {α : Type u} (xs ys : List α) (k : Nat) : Prop :=
  (∃ zs, zs <+ xs ∧ zs <+ ys ∧ zs.length = k) ∧
    ∀ zs, zs <+ xs → zs <+ ys → zs.length ≤ k

private lemma optimal_cons {α : Type u} {xs ys : List α} {k : Nat}
    (h : CellOptimal xs ys k) (a : α) : CellOptimal (a :: xs) (a :: ys) (k + 1) := by
  obtain ⟨⟨w, hx, hy, hw⟩, bound⟩ := h
  refine ⟨⟨a :: w, hx.cons_cons a, hy.cons_cons a, by simp [hw]⟩, ?_⟩
  intro zs hx hy
  cases zs with
  | nil => simp
  | cons z zs =>
    have hb := bound zs hx.of_cons_cons hy.of_cons_cons
    simpa using Nat.succ_le_succ hb

private lemma common_cons_ne {α : Type u} {xs ys zs : List α} {a b : α}
    (hab : a ≠ b) (hx : zs <+ a :: xs) (hy : zs <+ b :: ys) :
    (zs <+ xs ∧ zs <+ b :: ys) ∨ (zs <+ a :: xs ∧ zs <+ ys) := by
  cases hx with
  | cons _ hx => exact Or.inl ⟨hx, hy⟩
  | cons_cons _ hx =>
    cases hy with
    | cons _ hy => exact Or.inr ⟨hx.cons_cons _, hy⟩
    | cons_cons _ hy => exact (hab rfl).elim

private lemma optimal_cons_ne {α : Type u} {xs ys : List α} {a b : α} {up left : Nat}
    (hab : a ≠ b) (hu : CellOptimal xs (b :: ys) up)
    (hl : CellOptimal (a :: xs) ys left) :
    CellOptimal (a :: xs) (b :: ys) (max up left) := by
  obtain ⟨⟨u, hux, huy, huLen⟩, ub⟩ := hu
  obtain ⟨⟨l, hlx, hly, hlLen⟩, lb⟩ := hl
  constructor
  · by_cases h : up ≤ left
    · exact ⟨l, hlx, hly.cons b, by omega⟩
    · exact ⟨u, hux.cons a, huy, by omega⟩
  · intro w hx hy
    obtain h | h := common_cons_ne hab hx hy
    · have hb := ub w h.1 h.2
      omega
    · have hb := lb w h.1 h.2
      omega

private lemma optimal_reverse {α : Type u} {xs ys : List α} {k : Nat}
    (h : CellOptimal xs ys k) : CellOptimal xs.reverse ys.reverse k := by
  obtain ⟨⟨w, hx, hy, hw⟩, bound⟩ := h
  refine ⟨⟨w.reverse, hx.reverse, hy.reverse, by simpa using hw⟩, ?_⟩
  intro w hx hy
  simpa using bound w.reverse (by simpa using hx.reverse) (by simpa using hy.reverse)

private lemma optimal_append {α : Type u} {xs ys : List α} {k : Nat}
    (h : CellOptimal xs ys k) (a : α) :
    CellOptimal (xs ++ [a]) (ys ++ [a]) (k + 1) := by
  have h' := optimal_reverse (optimal_cons (optimal_reverse h) a)
  simpa using h'

private lemma optimal_append_ne {α : Type u} {xs ys : List α} {a b : α} {up left : Nat}
    (hab : a ≠ b) (hu : CellOptimal xs (ys ++ [b]) up)
    (hl : CellOptimal (xs ++ [a]) ys left) :
    CellOptimal (xs ++ [a]) (ys ++ [b]) (max up left) := by
  have hu' : CellOptimal xs.reverse (b :: ys.reverse) up := by
    simpa using optimal_reverse hu
  have hl' : CellOptimal (a :: xs.reverse) ys.reverse left := by
    simpa using optimal_reverse hl
  have h' := optimal_reverse (optimal_cons_ne hab hu' hl')
  simpa using h'

/-- Return the optimum common-subsequence length and one witness, using prefix dynamic programming.
The abstract time counts interior table transitions and nonterminal reconstruction transitions. -/
def longestCommonSubsequence {α : Type u} [BEq α] (xs ys : List α) :
    TimeM Nat (Nat × List α) :=
  let Row (n : Nat) : Type u :=
    ULift.{u} (Subtype (fun row : Array Nat => row.size = n + 1))
  let rec @[reducible] buildRow (x : α) (ys : Array α) (up : Row ys.size) :
      (j : Nat) → j ≤ ys.size → TimeM Nat (Row j)
    | 0, _ => pure ⟨⟨#[0], by simp⟩⟩
    | j + 1, hj => do
      let row ← buildRow x ys up j (by omega)
      TimeM.tick 1
      let value := if x == ys[j] then
        up.down.1[j]'(by rw [up.down.2]; omega) + 1
      else
        max (up.down.1[j + 1]'(by rw [up.down.2]; omega))
          (row.down.1[j]'(by rw [row.down.2]; omega))
      pure ⟨⟨row.down.1.push value, by simp [row.down.2]⟩⟩
  let Table (m n : Nat) : Type u :=
    ULift.{u} (Subtype (fun data : Array (Array Nat) =>
      data.size = m + 1 ∧ ∀ i (hi : i < data.size), data[i].size = n + 1))
  let cell {m n : Nat} (table : Table m n) (i j : Nat)
      (hi : i ≤ m) (hj : j ≤ n) : Nat :=
    (table.down.1[i]'(by rw [table.down.2.1]; omega))[j]'(by
      rw [table.down.2.2]; omega)
  let rec @[reducible] buildTable (xs ys : Array α) :
      (i : Nat) → i ≤ xs.size → TimeM Nat (Table i ys.size)
    | 0, _ => pure
      ⟨⟨#[Array.replicate (ys.size + 1) 0], by simp,
          by
            intro i hi
            have : i = 0 := by simpa using hi
            subst i
            simp⟩⟩
    | i + 1, hi => do
      let table ← buildTable xs ys i (by omega)
      let up : Row ys.size :=
        ⟨⟨table.down.1[i]'(by rw [table.down.2.1]; omega),
          table.down.2.2 i (by rw [table.down.2.1]; omega)⟩⟩
      let row ← buildRow (xs[i]'(by omega)) ys up ys.size (by omega)
      pure ⟨⟨table.down.1.push row.down.1, by simp [table.down.2.1], by
          intro k hk
          rw [Array.getElem_push]
          split
          · exact table.down.2.2 _ _
          · exact row.down.2⟩⟩
  let rec @[reducible] reconstruct (xs ys : Array α) (table : Table xs.size ys.size) :
      (i j : Nat) → i ≤ xs.size → j ≤ ys.size → List α → TimeM Nat (List α)
    | 0, _, _, _, acc => pure acc
    | _, 0, _, _, acc => pure acc
    | i + 1, j + 1, hi, hj, acc => do
      TimeM.tick 1
      if xs[i] == ys[j] then
        reconstruct xs ys table i j (by omega) (by omega) (xs[i] :: acc)
      else if cell table i (j + 1) (by omega) hj ≥ cell table (i + 1) j hi (by omega) then
        reconstruct xs ys table i (j + 1) (by omega) hj acc
      else
        reconstruct xs ys table (i + 1) j hi (by omega) acc
  termination_by i j _ _ _ => i + j
  do
    let table ← buildTable xs.toArray ys.toArray xs.toArray.size (by omega)
    let witness ← reconstruct xs.toArray ys.toArray table xs.toArray.size ys.toArray.size
      (by omega) (by omega) []
    pure (cell table xs.toArray.size ys.toArray.size (by omega) (by omega), witness)

private abbrev Row (n : Nat) :=
  ULift.{u} (Subtype (fun row : Array Nat => row.size = n + 1))

private abbrev Table (m n : Nat) :=
  ULift.{u} (Subtype (fun data : Array (Array Nat) =>
    data.size = m + 1 ∧ ∀ i (hi : i < data.size), data[i].size = n + 1))

private abbrev cell {m n : Nat} (table : Table m n) (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) : Nat :=
  (table.down.1[i]'(by rw [table.down.2.1]; omega))[j]'(by
    rw [table.down.2.2]; omega)

private lemma optimal_nil_left {α : Type u} (ys : List α) : CellOptimal [] ys 0 := by
  refine ⟨⟨[], by simp, by simp, rfl⟩, ?_⟩
  intro zs hz _
  have : zs = [] := List.sublist_nil.mp hz
  simp [this]

private lemma optimal_nil_right {α : Type u} (xs : List α) : CellOptimal xs [] 0 := by
  refine ⟨⟨[], by simp, by simp, rfl⟩, ?_⟩
  intro zs _ hz
  have : zs = [] := List.sublist_nil.mp hz
  simp [this]

private lemma buildRow_time {α : Type u} [BEq α] (x : α) (ys : Array α)
    (up : Row ys.size) (j : Nat) (hj : j ≤ ys.size) :
    (longestCommonSubsequence.buildRow x ys up j hj).time = j := by
  induction j with
  | zero => simp [longestCommonSubsequence.buildRow]
  | succ j ih =>
    simp only [longestCommonSubsequence.buildRow, TimeM.time_bind, TimeM.time_tick,
      TimeM.time_pure]
    rw [ih (by omega)]
    omega

private lemma buildTable_time {α : Type u} [BEq α] (xs ys : Array α)
    (i : Nat) (hi : i ≤ xs.size) :
    (longestCommonSubsequence.buildTable xs ys i hi).time = i * ys.size := by
  induction i with
  | zero => simp [longestCommonSubsequence.buildTable]
  | succ i ih =>
    simp only [longestCommonSubsequence.buildTable, TimeM.time_bind, TimeM.time_pure,
      buildRow_time]
    rw [ih (by omega), Nat.succ_mul]
    omega

private lemma buildRow_correct {α : Type u} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (ys : Array α) (up : Row ys.size)
    (hu : ∀ k (hk : k ≤ ys.size),
      CellOptimal xs (ys.toList.take k) (up.down.1[k]'(by rw [up.down.2]; omega)))
    (j : Nat) (hj : j ≤ ys.size) :
    ∀ k (hk : k ≤ j), CellOptimal (xs ++ [x]) (ys.toList.take k)
      ((longestCommonSubsequence.buildRow x ys up j hj).ret.down.1[k]'(by
        rw [(longestCommonSubsequence.buildRow x ys up j hj).ret.down.2]; omega)) := by
  induction j with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    simpa [longestCommonSubsequence.buildRow] using optimal_nil_right (xs ++ [x])
  | succ j ih =>
    intro k hk
    simp only [longestCommonSubsequence.buildRow, TimeM.ret_bind, TimeM.ret_pure]
    rw [Array.getElem_push]
    split
    · rename_i hlt
      exact ih (by omega) k (by
        have hs := (longestCommonSubsequence.buildRow x ys up j (by omega)).ret.down.2
        omega)
    · rename_i hnot
      have hsize := (longestCommonSubsequence.buildRow x ys up j (by omega)).ret.down.2
      have hkj : k = j + 1 := by omega
      subst k
      have hyp := ih (by omega) j (by omega)
      have hyj : j < ys.toList.length := by simpa using (show j < ys.size from by omega)
      rw [List.take_succ_eq_append_getElem hyj, Array.getElem_toList]
      split
      · rename_i heq
        have heq' : x = ys[j] := by simpa using heq
        subst x
        exact optimal_append (hu j (by omega)) _
      · rename_i hne
        have hne' : x ≠ ys[j] := by simpa using hne
        exact optimal_append_ne hne' (by
          simpa [List.take_succ_eq_append_getElem hyj] using hu (j + 1) (by omega)) hyp

private lemma buildTable_correct {α : Type u} [BEq α] [LawfulBEq α] (xs ys : Array α)
    (i : Nat) (hi : i ≤ xs.size) :
    ∀ p q (hp : p ≤ i) (hq : q ≤ ys.size),
      CellOptimal (xs.toList.take p) (ys.toList.take q)
        (cell (longestCommonSubsequence.buildTable xs ys i hi).ret p q hp hq) := by
  induction i with
  | zero =>
    intro p q hp hq
    have : p = 0 := by omega
    subst p
    simpa [longestCommonSubsequence.buildTable, cell] using
      optimal_nil_left (ys.toList.take q)
  | succ i ih =>
    intro p q hp hq
    simp only [longestCommonSubsequence.buildTable, TimeM.ret_bind, TimeM.ret_pure, cell]
    simp only [Array.getElem_push]
    split
    · rename_i hlt
      exact ih (by omega) p q (by
        have hs :=
          (longestCommonSubsequence.buildTable xs ys i (by omega)).ret.down.2.1
        omega) hq
    · rename_i hnot
      have hs := (longestCommonSubsequence.buildTable xs ys i (by omega)).ret.down.2.1
      have hpi : p = i + 1 := by omega
      subst p
      have hxi : i < xs.toList.length := by simpa using (show i < xs.size from by omega)
      rw [List.take_succ_eq_append_getElem hxi, Array.getElem_toList]
      let up : Row ys.size :=
        ⟨⟨(longestCommonSubsequence.buildTable xs ys i (by omega)).ret.down.1[i]'(by
          rw [(longestCommonSubsequence.buildTable xs ys i (by omega)).ret.down.2.1]; omega),
          (longestCommonSubsequence.buildTable xs ys i (by omega)).ret.down.2.2 i (by
            rw [(longestCommonSubsequence.buildTable xs ys i (by omega)).ret.down.2.1]; omega)⟩⟩
      exact buildRow_correct (xs.toList.take i) (xs[i]'(by omega)) ys up
        (fun k hk => ih (by omega) i k (by omega) hk) ys.size (by omega) q hq

private lemma reconstruct_time {α : Type u} [BEq α]
    (cellFn : ∀ {m n : Nat}, Table.{u} m n → (i j : Nat) → i ≤ m → j ≤ n → Nat)
    (xs ys : Array α)
    (table : Table xs.size ys.size) (i j : Nat) (hi : i ≤ xs.size) (hj : j ≤ ys.size)
    (acc : List α) :
    (longestCommonSubsequence.reconstruct cellFn xs ys table i j hi hj acc).time ≤ i + j := by
  fun_induction longestCommonSubsequence.reconstruct with
  | case1 => simp
  | case2 => simp
  | case3 i j hi hj acc ih1 ih2 ih3 =>
    simp only [TimeM.time_bind, TimeM.time_tick]
    split
    · omega
    · split <;> omega

private lemma optimal_unique {α : Type u} {xs ys : List α} {k l : Nat}
    (hk : CellOptimal xs ys k) (hl : CellOptimal xs ys l) : k = l := by
  obtain ⟨w, hx, hy, hw⟩ := hk.1
  obtain ⟨v, hvx, hvy, hv⟩ := hl.1
  have hkl := hl.2 w hx hy
  have hlk := hk.2 v hvx hvy
  omega

private lemma cell_match {α : Type u} [BEq α] [LawfulBEq α] (xs ys : Array α)
    (table : Table xs.size ys.size)
    (ho : ∀ p q (hp : p ≤ xs.size) (hq : q ≤ ys.size),
      CellOptimal (xs.toList.take p) (ys.toList.take q) (cell table p q hp hq))
    (i j : Nat) (hi : i + 1 ≤ xs.size) (hj : j + 1 ≤ ys.size)
    (heq : xs[i] = ys[j]) :
    cell table (i + 1) (j + 1) hi hj = cell table i j (by omega) (by omega) + 1 := by
  have hxi : i < xs.toList.length := by simpa using (show i < xs.size from by omega)
  have hyj : j < ys.toList.length := by simpa using (show j < ys.size from by omega)
  have hc := ho (i + 1) (j + 1) hi hj
  rw [List.take_succ_eq_append_getElem hxi, List.take_succ_eq_append_getElem hyj,
    Array.getElem_toList, Array.getElem_toList, ← heq] at hc
  exact optimal_unique hc (optimal_append (ho i j (by omega) (by omega)) _)

private lemma cell_nonmatch {α : Type u} [BEq α] [LawfulBEq α] (xs ys : Array α)
    (table : Table xs.size ys.size)
    (ho : ∀ p q (hp : p ≤ xs.size) (hq : q ≤ ys.size),
      CellOptimal (xs.toList.take p) (ys.toList.take q) (cell table p q hp hq))
    (i j : Nat) (hi : i + 1 ≤ xs.size) (hj : j + 1 ≤ ys.size)
    (hne : xs[i] ≠ ys[j]) :
    cell table (i + 1) (j + 1) hi hj =
      max (cell table i (j + 1) (by omega) hj) (cell table (i + 1) j hi (by omega)) := by
  have hxi : i < xs.toList.length := by simpa using (show i < xs.size from by omega)
  have hyj : j < ys.toList.length := by simpa using (show j < ys.size from by omega)
  have hc := ho (i + 1) (j + 1) hi hj
  have hu := ho i (j + 1) (by omega) hj
  have hl := ho (i + 1) j hi (by omega)
  rw [List.take_succ_eq_append_getElem hxi, List.take_succ_eq_append_getElem hyj,
    Array.getElem_toList, Array.getElem_toList] at hc
  rw [List.take_succ_eq_append_getElem hyj, Array.getElem_toList] at hu
  rw [List.take_succ_eq_append_getElem hxi, Array.getElem_toList] at hl
  exact optimal_unique hc (optimal_append_ne hne hu hl)

private lemma reconstruct_correct {α : Type u} [BEq α] [LawfulBEq α] (xs ys : Array α)
    (table : Table xs.size ys.size)
    (ho : ∀ p q (hp : p ≤ xs.size) (hq : q ≤ ys.size),
      CellOptimal (xs.toList.take p) (ys.toList.take q) (cell table p q hp hq))
    (i j : Nat) (hi : i ≤ xs.size) (hj : j ≤ ys.size) (acc : List α) :
    ∃ w, (longestCommonSubsequence.reconstruct cell xs ys table i j hi hj acc).ret =
      w ++ acc ∧
      w <+ xs.toList.take i ∧ w <+ ys.toList.take j ∧ w.length = cell table i j hi hj := by
  fun_induction longestCommonSubsequence.reconstruct with
  | case1 j _ hi acc hj _ =>
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    have hc := ho 0 j hi hj
    exact (optimal_unique (by simpa using hc) (optimal_nil_left _)).symm
  | case2 i _ hj acc hi _ _ =>
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    have hc := ho i 0 hi hj
    exact (optimal_unique (by simpa using hc) (optimal_nil_right _)).symm
  | case3 i j hi hj acc _ _ ih1 ih2 ih3 =>
    simp only [TimeM.ret_bind]
    have hxi : i < xs.toList.length := by simpa using (show i < xs.size from by omega)
    have hyj : j < ys.toList.length := by simpa using (show j < ys.size from by omega)
    split
    · rename_i heq
      have heq' : xs[i] = ys[j] := by simpa using heq
      obtain ⟨w, hret, hx, hy, hw⟩ := ih1
      refine ⟨w ++ [xs[i]], ?_, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using hret
      · rw [List.take_succ_eq_append_getElem hxi, Array.getElem_toList]
        exact hx.append_right _
      · rw [List.take_succ_eq_append_getElem hyj, Array.getElem_toList, ← heq']
        exact hy.append_right _
      · rw [List.length_append, List.length_singleton, hw, cell_match xs ys table ho i j hi hj heq']
    · rename_i hne
      have hne' : xs[i] ≠ ys[j] := by simpa using hne
      have hcell := cell_nonmatch xs ys table ho i j hi hj hne'
      split
      · rename_i hle
        obtain ⟨w, hret, hx, hy, hw⟩ := ih2
        refine ⟨w, hret, ?_, hy, ?_⟩
        · rw [List.take_succ_eq_append_getElem hxi]
          exact hx.trans (List.sublist_append_left _ _)
        · rw [hcell]
          omega
      · rename_i hlt
        obtain ⟨w, hret, hx, hy, hw⟩ := ih3
        refine ⟨w, hret, hx, ?_, ?_⟩
        · rw [List.take_succ_eq_append_getElem hyj]
          exact hy.trans (List.sublist_append_left _ _)
        · rw [hcell]
          omega

/-- The reported length equals the witness length, and the witness is a longest common sublist. -/
theorem longestCommonSubsequence_correct {α : Type u} [BEq α] [LawfulBEq α]
    (xs ys : List α) :
    let result := (longestCommonSubsequence xs ys).ret
    result.2.length = result.1 ∧ result.2 <+ xs ∧ result.2 <+ ys ∧
      (∀ zs, zs <+ xs → zs <+ ys → zs.length ≤ result.2.length) := by
  let table :=
    (longestCommonSubsequence.buildTable xs.toArray ys.toArray xs.toArray.size (by omega)).ret
  have ho := buildTable_correct xs.toArray ys.toArray xs.toArray.size (by omega)
  obtain ⟨w, hret, hx, hy, hw⟩ := reconstruct_correct xs.toArray ys.toArray table ho
    xs.toArray.size ys.toArray.size (by omega) (by omega) []
  have hc := ho xs.toArray.size ys.toArray.size (by omega) (by omega)
  simp only [List.size_toArray, List.take_length] at hx hy hc
  simp only [longestCommonSubsequence, TimeM.ret_bind, TimeM.ret_pure]
  change _ ∧ _ ∧ _ ∧ _
  have hr : (longestCommonSubsequence.reconstruct cell xs.toArray ys.toArray table
      xs.toArray.size ys.toArray.size (by omega) (by omega) []).ret = w := by
    simpa using hret
  rw [hr]
  exact ⟨hw, hx, hy, fun zs hzX hzY => by
    have hb := hc.2 zs hzX hzY
    simpa [hw] using hb⟩

/-- The number of table and reconstruction transitions is at most `m*n + (m+n)`. -/
theorem longestCommonSubsequence_time {α : Type u} [BEq α] (xs ys : List α) :
    (longestCommonSubsequence xs ys).time ≤ xs.length * ys.length + (xs.length + ys.length) := by
  simp only [longestCommonSubsequence, TimeM.time_bind, TimeM.time_pure, buildTable_time,
    List.size_toArray]
  apply Nat.add_le_add_left
  exact reconstruct_time
    (fun {m n} table i j hi hj =>
      (table.down.1[i]'(by rw [table.down.2.1]; omega))[j]'(by
        rw [table.down.2.2]; omega))
    xs.toArray ys.toArray
    (longestCommonSubsequence.buildTable xs.toArray ys.toArray xs.toArray.size (by omega)).ret
    xs.toArray.size ys.toArray.size (by omega) (by omega) []

end Cslib.Algorithms.Lean
