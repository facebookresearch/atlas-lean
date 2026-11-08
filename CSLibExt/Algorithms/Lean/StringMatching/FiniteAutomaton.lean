/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import CSLibExt.Algorithms.Lean.StringMatching.Naive

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-automaton all-occurrence string matching

CLRS fourth edition, Section 32.3, pp. 969-974: the displayed decreasing-candidate
constructor fills every transition row, including the accepting row. The scan binds
that completed table once and never resets after an acceptance, so overlaps are retained.
The automaton view uses canonical CSLib deterministic finite automata.

Symbols are Fin A; the row-major table is a root Vector indexed by q * A + a.
The empty pattern explicitly matches every boundary, including zero; an overlength
pattern has no matches. These are extensions matching the existing MatchAt specification.

The selected event count charges executed candidates, character comparisons, failed
decrements and table writes, then one lookup and acceptance test per consumed symbol
and one event per emitted shift. Character comparisons stop at the first mismatch.
Allocation, slicing, arithmetic, list construction and reversal are free in this model.
The scan's RAM interpretation assumes constant-time indexed access; this is not a
physical running-time, word/bit-cost or allocation-space theorem.

The constructor bound is cubic in pattern length times alphabet size. The improved
linear constructor mentioned by the source is a distinct algorithm, not this executor.
-/

public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.StringMatching

@[no_expose]
private def comparedEq {α : Type u} [DecidableEq α] : List α → List α → TimeM Nat Bool
  | [], [] => pure true
  | [], _ :: _ => pure false
  | _ :: _, [] => pure false
  | x :: xs, y :: ys => do
      TimeM.tick 1
      if x = y then comparedEq xs ys else pure false

private theorem comparedEq_ret {α : Type u} [DecidableEq α] (xs ys : List α) :
    (comparedEq xs ys).ret = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [comparedEq]
  | cons x xs ih =>
      cases ys with
      | nil => simp [comparedEq]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [comparedEq] using ih ys
          · simp [comparedEq, h]

private theorem comparedEq_time_le {α : Type u} [DecidableEq α] (xs ys : List α) :
    (comparedEq xs ys).time ≤ xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [comparedEq]
  | cons x xs ih =>
      cases ys with
      | nil => simp [comparedEq]
      | cons y ys =>
          by_cases h : x = y
          · simpa [comparedEq, h, Nat.add_comm] using Nat.add_le_add_right (ih ys) 1
          · simp [comparedEq, h]

@[no_expose]
private def suffixTest {α : Type u} [DecidableEq α] (pattern word : List α)
    (k : Nat) : TimeM Nat Bool :=
  comparedEq (pattern.take k) (word.drop (word.length - k))

private theorem suffixTest_ret {α : Type u} [DecidableEq α] (pattern word : List α)
    (k : Nat) (hk : k ≤ pattern.length) :
    (suffixTest pattern word k).ret = true ↔ pattern.take k <:+ word := by
  rw [suffixTest, comparedEq_ret, List.suffix_iff_eq_drop, List.length_take_of_le hk]

private theorem suffixTest_time_le {α : Type u} [DecidableEq α] (pattern word : List α)
    (k : Nat) : (suffixTest pattern word k).time ≤ k :=
  (comparedEq_time_le _ _).trans (List.length_take_le k pattern)

@[no_expose]
private def descendingSearch (test : Nat → TimeM Nat Bool) : Nat → TimeM Nat Nat
  | 0 => do
      TimeM.tick 1
      let _ ← test 0
      pure 0
  | k + 1 => do
      TimeM.tick 1
      let ok ← test (k + 1)
      if ok then pure (k + 1)
      else do
        TimeM.tick 1
        descendingSearch test k

private theorem descendingSearch_spec (test : Nat → TimeM Nat Bool)
    (hzero : (test 0).ret = true) (n : Nat) :
    IsGreatest {k | k ≤ n ∧ (test k).ret = true}
      (descendingSearch test n).ret := by
  induction n with
  | zero =>
      constructor
      · exact ⟨by simp [descendingSearch], hzero⟩
      · intro k hk
        simpa [descendingSearch] using hk.1
  | succ n ih =>
      by_cases h : (test (n + 1)).ret = true
      · rw [show (descendingSearch test (n + 1)).ret = n + 1 by
          simp [descendingSearch, h]]
        exact ⟨⟨le_rfl, h⟩, fun _ hk => hk.1⟩
      · rw [show (descendingSearch test (n + 1)).ret =
          (descendingSearch test n).ret by simp [descendingSearch, h]]
        constructor
        · exact ⟨ih.1.1.trans (Nat.le_succ n), ih.1.2⟩
        · intro k hk
          have hkn : k ≤ n := by
            by_contra hn
            have hkbound := hk.1
            have he : k = n + 1 := by omega
            exact h (he ▸ hk.2)
          exact ih.2 ⟨hkn, hk.2⟩

private theorem descendingSearch_time_le (test : Nat → TimeM Nat Bool)
    (hcost : ∀ k, (test k).time ≤ k) (n : Nat) :
    (descendingSearch test n).time + 1 ≤ 2 * (n + 1) ^ 2 := by
  induction n with
  | zero =>
      have hc := hcost 0
      simp [descendingSearch]
      omega
  | succ n ih =>
      have hc := hcost (n + 1)
      by_cases h : (test (n + 1)).ret = true
      · simp [descendingSearch, h]
        nlinarith
      · simp [descendingSearch, h]
        nlinarith

@[no_expose]
private def transitionCell {A : Nat} (pattern : List (Fin A)) (q : Nat) (a : Fin A) :
    TimeM Nat Nat :=
  descendingSearch (suffixTest pattern (pattern.take q ++ [a]))
    (min pattern.length (q + 1))

private theorem transitionCell_spec {A : Nat} (pattern : List (Fin A)) (q : Nat)
    (hq : q ≤ pattern.length) (a : Fin A) :
    IsGreatest {k | k ≤ pattern.length ∧ pattern.take k <:+ pattern.take q ++ [a]}
      (transitionCell pattern q a).ret := by
  have hs := descendingSearch_spec (suffixTest pattern (pattern.take q ++ [a]))
    ((suffixTest_ret _ _ 0 (Nat.zero_le _)).mpr (by simp))
    (min pattern.length (q + 1))
  change IsGreatest _
    (descendingSearch (suffixTest pattern (pattern.take q ++ [a]))
      (min pattern.length (q + 1))).ret
  constructor
  · have hbound := hs.1.1.trans (Nat.min_le_left _ _)
    exact ⟨hbound, (suffixTest_ret _ _ _ hbound).mp hs.1.2⟩
  · intro k hk
    apply hs.2
    constructor
    · apply Nat.le_min.mpr
      refine ⟨hk.1, ?_⟩
      have hlen := hk.2.length_le
      simpa [List.length_take_of_le hk.1, List.length_take_of_le hq] using hlen
    · exact (suffixTest_ret _ _ _ hk.1).mpr hk.2

private theorem vectorOfFnM_ret {α : Type u} {n : Nat} (f : Fin n → TimeM Nat α) :
    (Vector.ofFnM f).ret = Vector.ofFn (fun i => (f i).ret) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Vector.ofFnM_succ, Vector.ofFn_succ, ih, Fin.last]

private theorem vectorOfFnM_time {α : Type u} {n : Nat} (f : Fin n → TimeM Nat α) :
    (Vector.ofFnM f).time = ∑ i, (f i).time := by
  induction n with
  | zero => simp
  | succ n ih => simp [Vector.ofFnM_succ, ih, Fin.sum_univ_castSucc]

private theorem positiveAlphabet {A n : Nat} (i : Fin (n * A)) : 0 < A := by
  by_contra h
  have hA : A = 0 := Nat.eq_zero_of_not_pos h
  subst A
  simpa using i.isLt

@[no_expose]
private def rowOfIndex {A n : Nat} (i : Fin (n * A)) : Fin n :=
  ⟨i.val / A, (Nat.div_lt_iff_lt_mul (positiveAlphabet i)).mpr i.isLt⟩

@[no_expose]
private def columnOfIndex {A n : Nat} (i : Fin (n * A)) : Fin A :=
  ⟨i.val % A, Nat.mod_lt _ (positiveAlphabet i)⟩

@[no_expose]
private def flatIndex {A n : Nat} (q : Fin n) (a : Fin A) : Fin (n * A) :=
  ⟨q.val * A + a.val, by
    calc
      q.val * A + a.val < q.val * A + A := Nat.add_lt_add_left a.isLt _
      _ = (q.val + 1) * A := (Nat.succ_mul q.val A).symm
      _ ≤ n * A := Nat.mul_le_mul_right A (Nat.succ_le_of_lt q.isLt)⟩

private theorem row_flatIndex {A n : Nat} (q : Fin n) (a : Fin A) :
    rowOfIndex (flatIndex q a) = q := by
  apply Fin.ext
  change (q.val * A + a.val) / A = q.val
  rw [Nat.add_comm, Nat.add_mul_div_right a.val q.val
    (Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt), Nat.div_eq_of_lt a.isLt]
  simp

private theorem column_flatIndex {A n : Nat} (q : Fin n) (a : Fin A) :
    columnOfIndex (flatIndex q a) = a := by
  apply Fin.ext
  simp [columnOfIndex, flatIndex, Nat.add_mod, Nat.mod_eq_of_lt a.isLt]

@[no_expose]
private def typedTransitionCell {A : Nat} (pattern : List (Fin A))
    (q : Fin (pattern.length + 1)) (a : Fin A) : TimeM Nat (Fin (pattern.length + 1)) :=
  let r := transitionCell pattern q.val a
  { ret := ⟨r.ret, Nat.lt_succ_of_le
      (transitionCell_spec pattern q.val (Nat.le_of_lt_succ q.isLt) a).1.1⟩
    time := r.time }

/-- CLRS fourth edition section 32.3, decreasing-candidate row-major construction.
Each actual candidate comparison is charged by its executed equality tests.
-/
def computeTransition {A : Nat} (pattern : List (Fin A)) :
    TimeM Nat (Vector (Fin (pattern.length + 1)) ((pattern.length + 1) * A)) :=
  Vector.ofFnM fun i => do
    let q ← typedTransitionCell pattern (rowOfIndex i) (columnOfIndex i)
    TimeM.tick 1
    pure q

/-- Every actual table entry is the greatest feasible suffix-prefix length. -/
theorem computeTransition_spec {A : Nat} (pattern : List (Fin A))
    (q : Fin (pattern.length + 1)) (a : Fin A) :
    IsGreatest {k : Nat | k ≤ pattern.length ∧ pattern.take k <:+ pattern.take q.val ++ [a]}
      ((computeTransition pattern).ret.get ⟨q.val * A + a.val, by
        calc
          q.val * A + a.val < q.val * A + A := Nat.add_lt_add_left a.isLt _
          _ = (q.val + 1) * A := (Nat.succ_mul q.val A).symm
          _ ≤ (pattern.length + 1) * A :=
            Nat.mul_le_mul_right A (Nat.succ_le_of_lt q.isLt)⟩).val := by
  change IsGreatest _ ((computeTransition pattern).ret[(flatIndex q a).val]).val
  simpa [computeTransition, vectorOfFnM_ret, typedTransitionCell,
    row_flatIndex, column_flatIndex] using
    transitionCell_spec pattern q.val (Nat.le_of_lt_succ q.isLt) a

private theorem typedTransitionCell_time_le {A : Nat} (pattern : List (Fin A))
    (q : Fin (pattern.length + 1)) (a : Fin A) :
    (typedTransitionCell pattern q a).time + 1 ≤ 2 * (pattern.length + 1) ^ 2 := by
  have h := descendingSearch_time_le (suffixTest pattern (pattern.take q.val ++ [a]))
    (suffixTest_time_le _ _) (min pattern.length (q.val + 1))
  have hb : 2 * (min pattern.length (q.val + 1) + 1) ^ 2 ≤
      2 * (pattern.length + 1) ^ 2 := by
    gcongr
    exact Nat.min_le_left _ _
  simpa [typedTransitionCell, transitionCell] using h.trans hb

/-- Bound on the actual candidate/comparison/decrement/write event count. -/
theorem computeTransition_time_le {A : Nat} (pattern : List (Fin A)) :
    (computeTransition pattern).time ≤ 2 * A * (pattern.length + 1) ^ 3 := by
  unfold computeTransition
  rw [vectorOfFnM_time]
  calc
    _ ≤ ∑ _i : Fin ((pattern.length + 1) * A), 2 * (pattern.length + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa using typedTransitionCell_time_le pattern (rowOfIndex i) (columnOfIndex i)
    _ = 2 * A * (pattern.length + 1) ^ 3 := by
      simp
      ring

private theorem suffix_append_singleton {α : Type u} {xs ys : List α}
    (h : xs <:+ ys) (a : α) : xs ++ [a] <:+ ys ++ [a] := by
  obtain ⟨head, rfl⟩ := List.suffix_iff_exists_append_eq.mp h
  exact List.suffix_iff_exists_append_eq.mpr ⟨head, by simp [List.append_assoc]⟩

private theorem suffix_take_succ_iff {α : Type u} {pattern word : List α}
    {a : α} {k : Nat} (hk : k < pattern.length) :
    pattern.take (k + 1) <:+ word ++ [a] ↔
      pattern.take k <:+ word ∧ pattern[k] = a := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some]
  rw [List.suffix_iff_exists_append_eq]
  constructor
  · rintro ⟨head, h⟩
    have hparts : head ++ pattern.take k = word ∧ pattern[k] = a := by
      simpa only [← List.append_assoc, List.append_singleton_inj] using h
    exact ⟨List.suffix_iff_exists_append_eq.mpr ⟨head, hparts.1⟩, hparts.2⟩
  · rintro ⟨hs, he⟩
    obtain ⟨head, hhead⟩ := List.suffix_iff_exists_append_eq.mp hs
    exact ⟨head, by simp [← List.append_assoc, hhead, he]⟩

private theorem maximal_suffix_step {α : Type u} (pattern word : List α) (a : α)
    (q : Nat) (hq : IsGreatest {k | k ≤ pattern.length ∧ pattern.take k <:+ word} q)
    (r : Nat)
    (hr : IsGreatest
      {k | k ≤ pattern.length ∧ pattern.take k <:+ pattern.take q ++ [a]} r) :
    IsGreatest {k | k ≤ pattern.length ∧ pattern.take k <:+ word ++ [a]} r := by
  constructor
  · exact ⟨hr.1.1, hr.1.2.trans (suffix_append_singleton hq.1.2 a)⟩
  · intro k hk
    apply hr.2
    refine ⟨hk.1, ?_⟩
    have hkbound := hk.1
    cases k with
    | zero => simp
    | succ k =>
        have hklen : k < pattern.length := by omega
        have parts := (suffix_take_succ_iff hklen).mp hk.2
        have hkq : k ≤ q := hq.2 ⟨by omega, parts.1⟩
        have hsuffix : pattern.take k <:+ pattern.take q :=
          List.suffix_of_suffix_length_le parts.1 hq.1.2 (by
            simpa [List.length_take_of_le (by omega : k ≤ pattern.length),
              List.length_take_of_le hq.1.1] using hkq)
        exact (suffix_take_succ_iff hklen).mpr ⟨hsuffix, parts.2⟩

/-- Canonical deterministic automaton whose transition is the constructed table. -/
def patternAutomaton {A : Nat} (pattern : List (Fin A)) :
    Cslib.Automata.DA.FinAcc (Fin (pattern.length + 1)) (Fin A) :=
  let table := (computeTransition pattern).ret
  { start := 0
    tr := fun q a => table.get (flatIndex q a)
    accept := {q | q.val = pattern.length} }

private theorem patternAutomaton_step {A : Nat} (pattern word : List (Fin A))
    (a : Fin A) (q : Fin (pattern.length + 1))
    (hq : IsGreatest {k | k ≤ pattern.length ∧ pattern.take k <:+ word} q.val) :
    IsGreatest {k | k ≤ pattern.length ∧ pattern.take k <:+ word ++ [a]}
      ((patternAutomaton pattern).tr q a).val := by
  exact maximal_suffix_step pattern word a q.val hq _
    (computeTransition_spec pattern q a)

/-- The actual canonical automaton state is the greatest suffix-prefix length. -/
theorem patternAutomaton_state {A : Nat} (pattern word : List (Fin A)) :
    IsGreatest {k : Nat | k ≤ pattern.length ∧ pattern.take k <:+ word}
      ((patternAutomaton pattern).mtr (patternAutomaton pattern).start word).val := by
  induction word using List.reverseRecOn with
  | nil =>
      change IsGreatest {k : Nat | k ≤ pattern.length ∧ pattern.take k <:+ []} 0
      constructor
      · simp
      · intro k hk
        have hlen := hk.2.length_le
        simpa [List.length_take_of_le hk.1] using hlen
  | append_singleton word a ih =>
      rw [Cslib.FLTS.mtr_concat_eq]
      exact patternAutomaton_step pattern word a _ ih

@[no_expose]
private def scanStep {A m : Nat} (table : Vector (Fin (m + 1)) ((m + 1) * A))
    (q : Fin (m + 1)) (position : Nat) (out : TimeM Nat (List Nat)) (a : Fin A) :
    TimeM Nat (Fin (m + 1) × List Nat) := do
  let rev ← out
  TimeM.tick 1
  let next := table.get (flatIndex q a)
  TimeM.tick 1
  if next.val = m then do
    TimeM.tick 1
    pure (next, (position + 1 - m) :: rev)
  else pure (next, rev)

@[no_expose]
private def scan {A m : Nat} (table : Vector (Fin (m + 1)) ((m + 1) * A)) :
    Fin (m + 1) → Nat → TimeM Nat (List Nat) → List (Fin A) → TimeM Nat (List Nat)
  | _, _, out, [] => { ret := out.ret.reverse, time := out.time }
  | q, position, out, a :: rest =>
      let step := scanStep table q position out a
      scan table step.ret.1 (position + 1) { ret := step.ret.2, time := step.time } rest

private theorem scanStep_time {A m : Nat} (table : Vector (Fin (m + 1)) ((m + 1) * A))
    (q : Fin (m + 1)) (position : Nat) (out : TimeM Nat (List Nat)) (a : Fin A) :
    (scanStep table q position out a).time + out.ret.length =
      out.time + 2 + (scanStep table q position out a).ret.2.length := by
  by_cases h : (table.get (flatIndex q a)).val = m
  · simp [scanStep, h]
    omega
  · simp [scanStep, h]

private theorem scan_time {A m : Nat} (table : Vector (Fin (m + 1)) ((m + 1) * A))
    (q : Fin (m + 1)) (position : Nat) (out : TimeM Nat (List Nat)) (text : List (Fin A)) :
    (scan table q position out text).time + out.ret.length =
      out.time + 2 * text.length + (scan table q position out text).ret.length := by
  induction text generalizing q position out with
  | nil => simp [scan]
  | cons a rest ih =>
      let step := scanStep table q position out a
      have hstep := scanStep_time table q position out a
      have hrest := ih step.ret.1 (position + 1) {ret := step.ret.2, time := step.time}
      change (scan table step.ret.1 (position + 1)
        {ret := step.ret.2, time := step.time} rest).time + out.ret.length =
        out.time + 2 * (a :: rest).length +
          (scan table step.ret.1 (position + 1)
            {ret := step.ret.2, time := step.time} rest).ret.length
      change (scan table step.ret.1 (position + 1)
        {ret := step.ret.2, time := step.time} rest).time + step.ret.2.length =
        step.time + 2 * rest.length +
          (scan table step.ret.1 (position + 1)
            {ret := step.ret.2, time := step.time} rest).ret.length at hrest
      change step.time + out.ret.length = out.time + 2 + step.ret.2.length at hstep
      simp only [List.length_cons]
      omega

/-- All overlapping zero-based shifts, including every empty-pattern boundary.
The constructed table is bound once before the one-pass scan.
-/
def finiteAutomatonMatches {A : Nat} (pattern text : List (Fin A)) : TimeM Nat (List Nat) := do
  let table ← computeTransition pattern
  if pattern.length = 0 then do
    TimeM.tick 1
    scan table 0 0 (pure [0]) text
  else scan table 0 0 (pure []) text

/-- Exact candidate-table work, two events per symbol, and one event per output. -/
theorem finiteAutomatonMatches_time {A : Nat} (pattern text : List (Fin A)) :
    (finiteAutomatonMatches pattern text).time =
      (computeTransition pattern).time + 2 * text.length +
        (finiteAutomatonMatches pattern text).ret.length := by
  by_cases h : pattern.length = 0
  · have hs := scan_time (computeTransition pattern).ret 0 0 (pure [0]) text
    simp at hs
    simp [finiteAutomatonMatches, h]
    omega
  · have hs := scan_time (computeTransition pattern).ret 0 0 (pure []) text
    simp at hs
    simp [finiteAutomatonMatches, h, hs, Nat.add_assoc]

private theorem greatest_accept {α : Type u} (pattern word : List α) (q : Nat)
    (hq : IsGreatest {k | k ≤ pattern.length ∧ pattern.take k <:+ word} q) :
    q = pattern.length ↔ pattern <:+ word := by
  constructor
  · intro he
    simpa [he] using hq.1.2
  · intro hs
    exact Nat.le_antisymm hq.1.1 (hq.2 ⟨le_rfl, by simpa using hs⟩)

private theorem scanStep_state {A m : Nat} (table : Vector (Fin (m + 1)) ((m + 1) * A))
    (q : Fin (m + 1)) (position : Nat) (out : TimeM Nat (List Nat)) (a : Fin A) :
    (scanStep table q position out a).ret.1 = table.get (flatIndex q a) := by
  by_cases h : (table.get (flatIndex q a)).val = m <;> simp [scanStep, h]

@[no_expose]
private def endOffsets {A : Nat} (pattern text : List (Fin A)) (start count : Nat) : List Nat :=
  ((List.range' start count).filter (fun i => decide (pattern <:+ text.take i))).map
    (fun i => i - pattern.length)

private theorem endOffsets_pairwise {A : Nat} (pattern text : List (Fin A))
    (start count : Nat) : (endOffsets pattern text start count).Pairwise (· < ·) := by
  unfold endOffsets
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ List.pairwise_lt_range')
  intro i j hi _hj hij
  have hs : pattern <:+ text.take i := by simpa using (List.mem_filter.mp hi).2
  have hm : pattern.length ≤ i := hs.length_le.trans (List.length_take_le i text)
  omega

private theorem endOffsets_cons {A : Nat} (pattern built : List (Fin A)) (a : Fin A)
    (rest : List (Fin A)) :
    endOffsets pattern (built ++ a :: rest) (built.length + 1) (rest.length + 1) =
      if pattern <:+ built ++ [a] then
        (built.length + 1 - pattern.length) ::
          endOffsets pattern ((built ++ [a]) ++ rest) (built.length + 1 + 1) rest.length
      else endOffsets pattern ((built ++ [a]) ++ rest) (built.length + 1 + 1) rest.length := by
  have htake : (built ++ a :: rest).take (built.length + 1) = built ++ [a] := by
    simp [List.take_append, List.take_of_length_le (Nat.le_succ built.length)]
  by_cases h : pattern <:+ built ++ [a]
  · simp [endOffsets, List.range'_succ, htake, h, List.append_assoc]
  · simp [endOffsets, List.range'_succ, htake, h, List.append_assoc]

private theorem scan_ret {A : Nat} (pattern built rest : List (Fin A))
    (out : TimeM Nat (List Nat)) :
    (scan (computeTransition pattern).ret
      ((patternAutomaton pattern).mtr (patternAutomaton pattern).start built)
      built.length out rest).ret =
      out.ret.reverse ++ endOffsets pattern (built ++ rest) (built.length + 1) rest.length := by
  induction rest generalizing built out with
  | nil => simp [scan, endOffsets]
  | cons a rest ih =>
      let table := (computeTransition pattern).ret
      let q := (patternAutomaton pattern).mtr (patternAutomaton pattern).start built
      let step := scanStep table q built.length out a
      have hstate : step.ret.1 =
          (patternAutomaton pattern).mtr (patternAutomaton pattern).start (built ++ [a]) := by
        rw [Cslib.FLTS.mtr_concat_eq]
        exact scanStep_state table q built.length out a
      have hrest := ih (built ++ [a]) {ret := step.ret.2, time := step.time}
      simp only [List.length_append, List.length_singleton] at hrest
      rw [← hstate] at hrest
      change (scan table step.ret.1 (built.length + 1)
        {ret := step.ret.2, time := step.time} rest).ret = _
      rw [hrest]
      simp only [List.length_cons]
      rw [endOffsets_cons]
      have hacc : (table.get (flatIndex q a)).val = pattern.length ↔
          pattern <:+ built ++ [a] :=
        greatest_accept pattern (built ++ [a]) _
          (patternAutomaton_step pattern built a q (patternAutomaton_state pattern built))
      by_cases hs : pattern <:+ built ++ [a]
      · have he := hacc.mpr hs
        simp [step, scanStep, he, hs, List.append_assoc]
      · have he : (table.get (flatIndex q a)).val ≠ pattern.length := by
          intro he
          exact hs (hacc.mp he)
        simp [step, scanStep, he, hs]

private theorem finiteAutomatonMatches_endOffsets {A : Nat} (pattern text : List (Fin A)) :
    (finiteAutomatonMatches pattern text).ret =
      endOffsets pattern text 0 (text.length + 1) := by
  have hs := scan_ret pattern [] text
  by_cases hm : pattern.length = 0
  · have hp : pattern = [] := by simpa using hm
    subst pattern
    have hs0 := hs (pure [0])
    simpa [finiteAutomatonMatches, patternAutomaton, endOffsets, List.range'_succ] using hs0
  · have hs0 := hs (pure [])
    have hn : ¬ pattern <:+ ([] : List (Fin A)) := by
      intro h
      exact hm (Nat.eq_zero_of_le_zero (by simpa using h.length_le))
    simpa [finiteAutomatonMatches, patternAutomaton, hm, endOffsets, List.range'_succ, hn] using hs0

private theorem matchAt_end_iff {α : Type u} (pattern text : List α) (offset : Nat) :
    MatchAt pattern text offset ↔
      offset + pattern.length ≤ text.length ∧
        pattern <:+ text.take (offset + pattern.length) := by
  constructor
  · rintro ⟨hoffset, hp⟩
    have hl := hp.length_le
    simp only [List.length_drop] at hl
    refine ⟨by omega, ?_⟩
    rw [List.take_add, ← List.prefix_iff_eq_take.mp hp]
    exact List.suffix_append _ _
  · rintro ⟨hend, hs⟩
    have he := List.suffix_iff_eq_drop.mp hs
    have hl : (text.take (offset + pattern.length)).length = offset + pattern.length := by
      simp [List.length_take, Nat.min_eq_left hend]
    rw [hl, Nat.add_sub_cancel_right, List.drop_take, Nat.add_sub_cancel_left] at he
    exact ⟨by omega, List.prefix_iff_eq_take.mpr he⟩

private theorem mem_endOffsets_iff {A : Nat} (pattern text : List (Fin A)) (offset : Nat) :
    offset ∈ endOffsets pattern text 0 (text.length + 1) ↔ MatchAt pattern text offset := by
  unfold endOffsets
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hs⟩, he⟩
    have hi' : i ≤ text.length := by
      rcases List.mem_range'.mp hi with ⟨j, hj, hij⟩
      simp at hij
      omega
    have hm : pattern.length ≤ i := hs.length_le.trans (List.length_take_le i text)
    apply (matchAt_end_iff pattern text offset).mpr
    have he' : offset + pattern.length = i := by omega
    exact ⟨by omega, by simpa [he'] using hs⟩
  · intro hm
    obtain ⟨hend, hs⟩ := (matchAt_end_iff pattern text offset).mp hm
    refine ⟨offset + pattern.length, ⟨?_, hs⟩, by omega⟩
    exact List.mem_range'.mpr ⟨offset + pattern.length, by omega, by simp⟩

/-- The complete increasing list of zero-based shifts, including overlaps and empty boundaries. -/
theorem finiteAutomatonMatches_ret {A : Nat} (pattern text : List (Fin A)) :
    (finiteAutomatonMatches pattern text).ret = (TimeM.naiveMatches pattern text).ret := by
  rw [finiteAutomatonMatches_endOffsets]
  apply List.Pairwise.eq_of_mem_iff (endOffsets_pairwise pattern text 0 (text.length + 1))
    (TimeM.naiveMatches_pairwise pattern text)
  intro offset
  exact (mem_endOffsets_iff pattern text offset).trans
    (TimeM.mem_naiveMatches_iff pattern text offset).symm

end Cslib.Algorithms.Lean.StringMatching

end
