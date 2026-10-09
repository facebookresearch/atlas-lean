/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.Array.Match
public import Batteries.Data.List.Basic
public import CSLibExt.Algorithms.Lean.StringMatching.Basic
public import Cslib.Algorithms.Lean.TimeM

import Batteries.Data.List.Lemmas

/-!
# Knuth-Morris-Pratt string matching

This module uses Batteries' prefix table and transition. Its cost counts one unit for every
symbol comparison performed while constructing the table or scanning the text; list operations,
array access, arithmetic, and control flow are free.

## Implementation notes

`kmpSearch` is opaque to downstream modules; its timed construction and scan recursors are private.
The kernel-checked semantic bridge uses transparent `List.dropInfix?`. No equality is claimed with
the pinned opaque Batteries matcher, whose empty-pattern behavior also differs from this API.
The prefix-table representation and operations adapt `Array.PrefixTable`,
`Array.PrefixTable.step`, `Array.PrefixTable.extend`, and `Array.mkPrefixTable` from Batteries
revision `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`.

## References

- Donald E. Knuth, James H. Morris, Jr., and Vaughan R. Pratt, “Fast Pattern Matching in Strings,”
  *SIAM Journal on Computing* 6(2), 323–350 (1977), DOI 10.1137/0206024.
-/
set_option autoImplicit false
namespace Cslib.Algorithms.Lean.TimeM
universe u
variable {α : Type u}
private def timedStep [BEq α] (table : Array.PrefixTable α) (x : α) :
    Fin (table.size + 1) → TimeM Nat (Fin (table.size + 1))
  | ⟨k, hk⟩ =>
      let fallback := fun () =>
        match k with
        | 0 => pure ⟨0, Nat.zero_lt_succ _⟩
        | k + 1 =>
            have hindex : k < table.size := Nat.lt_of_succ_lt_succ hk
            let next := table.toArray[k].2
            have hnext : next < k + 1 := Nat.lt_succ_of_le (table.valid hindex)
            timedStep table x ⟨next, Nat.lt_trans hnext hk⟩
      if hsize : k < table.size then do
        ✓
        if x == table.toArray[k].1 then
          return ⟨k + 1, Nat.succ_lt_succ hsize⟩
        else
          fallback ()
      else
        fallback ()
termination_by state => state.val
private def extendWith (table : Array.PrefixTable α) (x : α)
    (failure : Fin (table.size + 1)) : Array.PrefixTable α where
  toArray := table.toArray.push (x, failure.val)
  valid _ := by
    rw [Array.getElem_push]
    split
    · exact table.valid ..
    · next h =>
      exact Nat.le_trans (Nat.lt_succ_iff.1 failure.isLt) (Nat.not_lt.1 h)
private def timedBuildFrom [BEq α] (table : Array.PrefixTable α) :
    List α → TimeM Nat (Array.PrefixTable α)
  | [] => pure table
  | x :: xs =>
      let step := timedStep table x ⟨table.size, Nat.lt_succ_self _⟩
      let rest := timedBuildFrom (extendWith table x step.ret) xs
      ⟨rest.ret, step.time + rest.time⟩
private def timedScan [BEq α] (table : Array.PrefixTable α) (offset : Nat)
    (state : Fin (table.size + 1)) : List α → TimeM Nat (Option Nat)
  | [] => pure none
  | x :: xs => do
      let next ← timedStep table x state
      if next = table.size then
        return some (offset + 1 - table.size)
      else
        timedScan table (offset + 1) next xs

/-- Returns the first zero-based occurrence of `pattern` in `text`, charging only symbol
comparisons. The empty pattern occurs at offset zero with cost zero. -/
public def kmpSearch [BEq α] (pattern text : List α) : TimeM Nat (Option Nat) :=
  match pattern with
  | [] => pure (some 0)
  | _ :: _ =>
      let table := timedBuildFrom default pattern
      let result := timedScan table.ret 0 0 text
      ⟨result.ret, table.time + result.time⟩
end Cslib.Algorithms.Lean.TimeM
@[expose] public section
namespace Cslib.Algorithms.Lean.TimeM
universe u
variable {α : Type u}
private theorem ret_timedStep [BEq α] (table : Array.PrefixTable α) (x : α)
    (state : Fin (table.size + 1)) :
    (timedStep table x state).ret = table.step x state := by
  induction hstate : state.val using Nat.strong_induction_on generalizing state with
  | h k ih =>
      obtain ⟨state, hstateSize⟩ := state
      simp only at hstate
      subst k
      rw [timedStep.eq_def, Array.PrefixTable.step.eq_def]
      by_cases hsize : state < table.size
      · simp only [hsize, ↓reduceDIte, TimeM.ret_bind]
        by_cases heq : (x == table.toArray[state].1) = true
        · simp only [heq, ite_true, TimeM.ret_pure]
        · simp only [heq]
          cases state with
          | zero => rfl
          | succ k =>
              have hindex : k < table.size := Nat.lt_of_succ_lt_succ hstateSize
              let next := (table.toArray[k]'hindex).2
              have hnext : next < k + 1 := Nat.lt_succ_of_le (table.valid hindex)
              exact ih next hnext ⟨next, hnext.trans hstateSize⟩ rfl
      · simp only [hsize, ↓reduceDIte]
        cases state with
        | zero => rfl
        | succ k =>
            have hindex : k < table.size := Nat.lt_of_succ_lt_succ hstateSize
            let next := (table.toArray[k]'hindex).2
            have hnext : next < k + 1 := Nat.lt_succ_of_le (table.valid hindex)
            exact ih next hnext ⟨next, hnext.trans hstateSize⟩ rfl
private theorem ret_timedBuildFrom [BEq α] (table : Array.PrefixTable α) (xs : List α) :
    (timedBuildFrom table xs).ret = xs.foldl (·.extend) table := by
  induction xs generalizing table with
  | nil => rfl
  | cons x xs ih =>
      rw [timedBuildFrom.eq_def, List.foldl_cons]
      simpa [extendWith, Array.PrefixTable.extend, ret_timedStep] using ih (table.extend x)
private theorem ret_timedBuild [BEq α] (pattern : List α) :
    (timedBuildFrom default pattern).ret = Array.mkPrefixTable pattern.toArray := by
  rw [ret_timedBuildFrom]
  simp only [Array.mkPrefixTable, List.foldl_toArray]
private theorem prefixTable_extend_size [BEq α] (table : Array.PrefixTable α) (x : α) :
    (table.extend x).size = table.size + 1 := by
  change (table.toArray.push _).size = table.toArray.size + 1
  exact Array.size_push _
private theorem prefixTable_extend_symbols [BEq α] (table : Array.PrefixTable α) (x : α) :
    (table.extend x).toArray.toList.map Prod.fst =
      table.toArray.toList.map Prod.fst ++ [x] := by
  change (table.toArray.push _).toList.map Prod.fst = _
  rw [Array.toList_push, List.map_append]
  rfl
private theorem prefixTable_fold_size [BEq α] (table : Array.PrefixTable α) (xs : List α) :
    (xs.foldl (·.extend) table).size = table.size + xs.length := by
  induction xs generalizing table with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, prefixTable_extend_size]
      simp only [List.length_cons]
      omega
private theorem prefixTable_fold_symbols [BEq α] (table : Array.PrefixTable α)
    (xs : List α) :
    (xs.foldl (·.extend) table).toArray.toList.map Prod.fst =
      table.toArray.toList.map Prod.fst ++ xs := by
  induction xs generalizing table with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, prefixTable_extend_symbols]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

end Cslib.Algorithms.Lean.TimeM

namespace Array

universe u

/-- The KMP prefix table has one entry for every pattern symbol. -/
@[simp]
theorem mkPrefixTable_size {α : Type u} [BEq α] (pattern : List α) :
    (mkPrefixTable pattern.toArray).size = pattern.length := by
  rw [mkPrefixTable, List.foldl_toArray]
  have h := Cslib.Algorithms.Lean.TimeM.prefixTable_fold_size
    (default : PrefixTable α) pattern
  have hdefault : (default : PrefixTable α).size = 0 := by rfl
  rw [hdefault, Nat.zero_add] at h
  exact h

/-- Reading the first component of each prefix-table entry recovers the pattern. -/
theorem mkPrefixTable_symbols {α : Type u} [BEq α] (pattern : List α) :
    (mkPrefixTable pattern.toArray).toArray.toList.map Prod.fst = pattern := by
  rw [mkPrefixTable, List.foldl_toArray]
  have h := Cslib.Algorithms.Lean.TimeM.prefixTable_fold_symbols
    (default : PrefixTable α) pattern
  have hdefault : (default : PrefixTable α).toArray.toList.map Prod.fst = [] := by
    change (#[] : Array (α × Nat)).toList.map Prod.fst = []
    rfl
  rw [hdefault, List.nil_append] at h
  exact h

end Array

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u}
private def IsPrefixTable (pattern : List α) (table : Array.PrefixTable α) : Prop :=
  table.size = pattern.length ∧
    table.toArray.toList.map Prod.fst = pattern ∧
    ∀ q (hq : q < table.size),
      let failure := table.toArray[q].2
      failure ≤ q ∧
        (pattern.take failure).IsSuffix (pattern.take (q + 1)) ∧
        ∀ k, k ≤ q →
          (pattern.take k).IsSuffix (pattern.take (q + 1)) → k ≤ failure
private lemma prefixTable_get_fst {pattern : List α} {table : Array.PrefixTable α}
    (hsize : table.size = pattern.length)
    (hsymbols : table.toArray.toList.map Prod.fst = pattern) (q : Nat)
    (hq : q < table.size) : table.toArray[q].1 = pattern[q]'(by omega) := by
  have hqList : q < table.toArray.toList.length := by simpa using hq
  have hqMap : q < (table.toArray.toList.map Prod.fst).length := by simpa using hqList
  have hqPattern : q < pattern.length := by omega
  calc
    table.toArray[q].1 = (table.toArray.toList[q]'hqList).1 := by rw [Array.getElem_toList]
    _ = (table.toArray.toList.map Prod.fst)[q]'hqMap := by rw [List.getElem_map]
    _ = pattern[q]'hqPattern := by
      have h := congrArg (fun xs : List α => xs[q]?) hsymbols
      rw [List.getElem?_eq_getElem hqMap, List.getElem?_eq_getElem hqPattern] at h
      exact Option.some.inj h
private lemma take_add_one_of_lt (pattern : List α) {k : Nat} (hk : k < pattern.length) :
    pattern.take (k + 1) = pattern.take k ++ [pattern[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp
private lemma suffix_append_singleton {xs ys : List α} (h : xs.IsSuffix ys) (x : α) :
    (xs ++ [x]).IsSuffix (ys ++ [x]) := by
  rw [List.suffix_iff_exists_append_eq] at h ⊢
  obtain ⟨head, rfl⟩ := h
  exact ⟨head, by simp only [List.append_assoc]⟩
private lemma suffix_take_add_one_iff {pattern consumed : List α} {x : α} {k : Nat}
    (hk : k < pattern.length) :
    (pattern.take (k + 1)).IsSuffix (consumed ++ [x]) ↔
      (pattern.take k).IsSuffix consumed ∧ pattern[k] = x := by
  rw [take_add_one_of_lt pattern hk, List.suffix_iff_exists_append_eq]
  constructor
  · rintro ⟨head, h⟩
    rw [← List.append_assoc, List.append_singleton_inj] at h
    exact ⟨List.suffix_iff_exists_append_eq.mpr ⟨head, h.1⟩, h.2⟩
  · rintro ⟨hsuffix, heq⟩
    obtain ⟨head, rfl⟩ := List.suffix_iff_exists_append_eq.mp hsuffix
    exact ⟨head, by simp only [List.append_assoc, heq]⟩
private lemma step_spec_aux [BEq α] [LawfulBEq α]
    {pattern consumed : List α} {table : Array.PrefixTable α} (x : α)
    (htable : IsPrefixTable pattern table) (state : Fin (table.size + 1))
    (hsuffix : (pattern.take state.val).IsSuffix consumed)
    (hupper : ∀ k, k ≤ pattern.length →
      (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ state.val + 1) :
    let next := table.step x state
    (pattern.take next.val).IsSuffix (consumed ++ [x]) ∧
      ∀ k, k ≤ pattern.length →
        (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ next.val := by
  induction hstate : state.val using Nat.strong_induction_on generalizing state consumed with
  | h stateValue ih =>
      obtain ⟨state, hstateSize⟩ := state
      simp only at hstate
      subst stateValue
      obtain ⟨htableSize, hsymbols, hfailures⟩ := htable
      rw [Array.PrefixTable.step.eq_def]
      by_cases hsize : state < table.size
      · simp only [hsize, ↓reduceDIte]
        have hentry := prefixTable_get_fst htableSize hsymbols state hsize
        by_cases heq : (x == table.toArray[state].1) = true
        · simp only [heq, ite_true]
          have hx : x = pattern[state] := (beq_iff_eq.mp heq).trans hentry
          constructor
          · rw [take_add_one_of_lt pattern (by omega), ← hx]
            exact suffix_append_singleton hsuffix x
          · intro k hk hsuffix'
            exact hupper k hk hsuffix'
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          have hcandidate : ∀ k, k ≤ pattern.length →
              (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ state := by
            intro k hk hsuffix'
            have hle := hupper k hk hsuffix'
            change k ≤ state + 1 at hle
            by_contra hnot
            have hkeq : k = state + 1 := by omega
            subst k
            have hparts := (suffix_take_add_one_iff (k := state) (by omega)).mp hsuffix'
            exact heq (beq_iff_eq.mpr (hparts.2.symm.trans hentry.symm))
          cases state with
          | zero =>
              constructor
              · simp
              · exact hcandidate
          | succ q =>
              have hindex : q < table.size := Nat.lt_of_succ_lt_succ hstateSize
              let failure := table.toArray[q].2
              have hfailureLt : failure < q + 1 :=
                Nat.lt_succ_of_le (table.valid hindex)
              have hfailureSpec := hfailures q hindex
              have hfailureSuffix : (pattern.take failure).IsSuffix consumed :=
                hfailureSpec.2.1.trans (by simpa using hsuffix)
              have hfailureUpper : ∀ k, k ≤ pattern.length →
                  (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ failure + 1 := by
                intro k hk hsuffix'
                have hkState := hcandidate k hk hsuffix'
                by_cases hkzero : k = 0
                · omega
                · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
                  have hrLength : r < pattern.length := by omega
                  have hrSuffix :=
                    (suffix_take_add_one_iff (k := r) hrLength).mp hsuffix' |>.1
                  have hrTake : (pattern.take r).IsSuffix (pattern.take (q + 1)) := by
                    apply List.suffix_of_suffix_length_le hrSuffix (by simpa using hsuffix)
                    simp only [List.length_take]
                    omega
                  have hrFailure := hfailureSpec.2.2 r (by omega) hrTake
                  omega
              exact ih failure hfailureLt ⟨failure, hfailureLt.trans hstateSize⟩
                hfailureSuffix hfailureUpper rfl
      · simp only [hsize, ↓reduceDIte]
        have hcandidate : ∀ k, k ≤ pattern.length →
            (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ state := by
          intro k hk _
          omega
        cases state with
        | zero =>
            constructor
            · simp
            · exact hcandidate
        | succ q =>
            have hindex : q < table.size := Nat.lt_of_succ_lt_succ hstateSize
            let failure := table.toArray[q].2
            have hfailureLt : failure < q + 1 :=
              Nat.lt_succ_of_le (table.valid hindex)
            have hfailureSpec := hfailures q hindex
            have hfailureSuffix : (pattern.take failure).IsSuffix consumed :=
              hfailureSpec.2.1.trans (by simpa using hsuffix)
            have hfailureUpper : ∀ k, k ≤ pattern.length →
                (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ failure + 1 := by
              intro k hk hsuffix'
              have hkState := hcandidate k hk hsuffix'
              by_cases hkzero : k = 0
              · omega
              · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
                have hrLength : r < pattern.length := by omega
                have hrSuffix :=
                  (suffix_take_add_one_iff (k := r) hrLength).mp hsuffix' |>.1
                have hrTake : (pattern.take r).IsSuffix (pattern.take (q + 1)) := by
                  apply List.suffix_of_suffix_length_le hrSuffix (by simpa using hsuffix)
                  simp only [List.length_take]
                  omega
                have hrFailure := hfailureSpec.2.2 r (by omega) hrTake
                omega
            exact ih failure hfailureLt ⟨failure, hfailureLt.trans hstateSize⟩
              hfailureSuffix hfailureUpper rfl
private lemma step_spec [BEq α] [LawfulBEq α]
    {pattern consumed : List α} {table : Array.PrefixTable α}
    (htable : IsPrefixTable pattern table) (x : α)
    (state : Fin (table.size + 1))
    (hstate : state.val ≤ pattern.length ∧
      (pattern.take state.val).IsSuffix consumed ∧
      ∀ k, k ≤ pattern.length →
        (pattern.take k).IsSuffix consumed → k ≤ state.val) :
    let next := table.step x state
    next.val ≤ pattern.length ∧
      (pattern.take next.val).IsSuffix (consumed ++ [x]) ∧
      ∀ k, k ≤ pattern.length →
        (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ next.val := by
  have hupper : ∀ k, k ≤ pattern.length →
      (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ state.val + 1 := by
    intro k hk hsuffix
    by_cases hkzero : k = 0
    · omega
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
      have hrLength : r < pattern.length := by omega
      have hrSuffix := (suffix_take_add_one_iff (k := r) hrLength).mp hsuffix |>.1
      have hrState := hstate.2.2 r (by omega) hrSuffix
      omega
  have hstep := step_spec_aux x htable state hstate.2.1 hupper
  have hnext := (table.step x state).isLt
  have htableSize : table.size = pattern.length := htable.1
  have hnextLe : (table.step x state).val ≤ pattern.length := by omega
  exact ⟨hnextLe, hstep⟩
private lemma isPrefixTable_default [BEq α] [LawfulBEq α] :
    IsPrefixTable ([] : List α) default := by
  refine ⟨rfl, rfl, ?_⟩
  intro q hq
  change q < 0 at hq
  omega
private lemma isPrefixTable_extend [BEq α] [LawfulBEq α]
    {pattern : List α} {table : Array.PrefixTable α} (x : α)
    (htable : IsPrefixTable pattern table) :
    IsPrefixTable (pattern ++ [x]) (table.extend x) := by
  obtain ⟨htableSize, hsymbols, hfailures⟩ := htable
  have hextendSize : (table.extend x).size = table.size + 1 := by
    change (table.toArray.push _).size = table.toArray.size + 1
    exact Array.size_push _
  have hextendSymbols :
      (table.extend x).toArray.toList.map Prod.fst =
        table.toArray.toList.map Prod.fst ++ [x] := by
    change (table.toArray.push _).toList.map Prod.fst = _
    rw [Array.toList_push, List.map_append]
    rfl
  refine ⟨by simp [hextendSize, htableSize], by simpa [hsymbols] using hextendSymbols, ?_⟩
  intro q hq
  by_cases hqOld : q < table.size
  · have hfailure := hfailures q hqOld
    have hentry : (table.extend x).toArray[q].2 = table.toArray[q].2 := by
      let entry := (x, (table.step x ⟨table.size, Nat.lt_succ_self _⟩).val)
      have hqPush : q < (table.toArray.push entry).size := by
        rw [Array.size_push]
        exact Nat.lt_succ_of_lt hqOld
      have hget : (table.toArray.push entry)[q]'hqPush = table.toArray[q]'hqOld := by
        simp only [Array.getElem_push, hqOld, ↓reduceDIte]
      exact congrArg Prod.snd hget
    rw [hentry]
    refine ⟨hfailure.1, ?_, ?_⟩
    · rw [List.take_append_of_le_length (by omega),
        List.take_append_of_le_length (by omega)]
      exact hfailure.2.1
    · intro k hk hsuffix
      rw [List.take_append_of_le_length (by omega),
        List.take_append_of_le_length (by omega)] at hsuffix
      exact hfailure.2.2 k hk hsuffix
  · have hqEq : q = table.size := by omega
    subst q
    let state : Fin (table.size + 1) := ⟨table.size, Nat.lt_succ_self _⟩
    have hstate : state.val ≤ pattern.length ∧
        (pattern.take state.val).IsSuffix pattern ∧
        ∀ k, k ≤ pattern.length → (pattern.take k).IsSuffix pattern → k ≤ state.val := by
      refine ⟨by simp [state, htableSize], ?_, ?_⟩
      · simp [state, htableSize]
      · intro k hk _
        simpa [state, htableSize] using hk
    have hstep := step_spec ⟨htableSize, hsymbols, hfailures⟩ x state hstate
    have hentry : (table.extend x).toArray[table.size].2 = (table.step x state).val := by
      let entry := (x, (table.step x state).val)
      have hqPush : table.size < (table.toArray.push entry).size := by
        rw [Array.size_push]
        exact Nat.lt_succ_self _
      have hget : (table.toArray.push entry)[table.size]'hqPush = entry := by
        simp only [Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte]
      exact congrArg Prod.snd hget
    have hfull : (pattern ++ [x]).take (table.size + 1) = pattern ++ [x] := by
      rw [htableSize]
      have hlength : pattern.length + 1 = (pattern ++ [x]).length := by simp
      rw [hlength, List.take_length]
    rw [hentry]
    refine ⟨by simpa [htableSize] using hstep.1, ?_, ?_⟩
    · rw [List.take_append_of_le_length hstep.1]
      rw [hfull]
      simpa [state] using hstep.2.1
    · intro k hk hsuffix
      rw [List.take_append_of_le_length (l₁ := pattern) (l₂ := [x]) (by omega),
        hfull] at hsuffix
      exact hstep.2.2 k (by omega) hsuffix
private lemma isPrefixTable_fold [BEq α] [LawfulBEq α]
    (built xs : List α) (table : Array.PrefixTable α)
    (htable : IsPrefixTable built table) :
    IsPrefixTable (built ++ xs) (xs.foldl (·.extend) table) := by
  induction xs generalizing built table with
  | nil => simpa using htable
  | cons x xs ih =>
      rw [List.foldl_cons]
      have hextend := isPrefixTable_extend x htable
      simpa only [List.append_assoc, List.singleton_append] using
        ih (built ++ [x]) (table.extend x) hextend
private theorem isPrefixTable_mkPrefixTable [BEq α] [LawfulBEq α]
    (pattern : List α) : IsPrefixTable pattern (Array.mkPrefixTable pattern.toArray) := by
  rw [Array.mkPrefixTable, List.foldl_toArray]
  simpa using isPrefixTable_fold ([] : List α) pattern default isPrefixTable_default
private theorem prefixTable_failure_spec_internal [BEq α] [LawfulBEq α]
    (pattern : List α) (q : Nat) (hq : q < pattern.length) :
    let table := Array.mkPrefixTable pattern.toArray
    let failure := table.toArray[q]'(by
      change q < (Array.mkPrefixTable pattern.toArray).size
      rw [Array.mkPrefixTable_size]
      exact hq) |>.2
    failure ≤ q ∧
      (pattern.take failure).IsSuffix (pattern.take (q + 1)) ∧
      ∀ k, k ≤ q → (pattern.take k).IsSuffix (pattern.take (q + 1)) → k ≤ failure := by
  have htable := isPrefixTable_mkPrefixTable pattern
  exact htable.2.2 q (by simpa [htable.1] using hq)
private theorem prefixTable_step_spec_internal [BEq α] [LawfulBEq α]
    (pattern consumed : List α) (x : α)
    (state : Fin ((Array.mkPrefixTable pattern.toArray).size + 1))
    (hstate : state.val ≤ pattern.length ∧
      (pattern.take state.val).IsSuffix consumed ∧
      ∀ k, k ≤ pattern.length → (pattern.take k).IsSuffix consumed → k ≤ state.val) :
    let table := Array.mkPrefixTable pattern.toArray
    let next := table.step x state
    next.val ≤ pattern.length ∧
      (pattern.take next.val).IsSuffix (consumed ++ [x]) ∧
      ∀ k, k ≤ pattern.length →
        (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ next.val :=
  step_spec (isPrefixTable_mkPrefixTable pattern) x state hstate
private def FirstEnd (pattern text : List α) (endOffset : Nat) : Prop :=
  endOffset ≤ text.length ∧
    pattern.IsSuffix (text.take endOffset) ∧
    ∀ earlier < endOffset, ¬pattern.IsSuffix (text.take earlier)
private lemma matchAt_suffix_take_add {pattern text : List α} {offset : Nat}
    (hmatch : Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text offset) :
    offset + pattern.length ≤ text.length ∧
      pattern.IsSuffix (text.take (offset + pattern.length)) := by
  obtain ⟨hoffset, hprefix⟩ := hmatch
  have hlength := hprefix.length_le
  simp only [List.length_drop] at hlength
  constructor
  · omega
  · rw [List.take_add, ← List.prefix_iff_eq_take.mp hprefix]
    exact List.suffix_append _ _
private lemma matchAt_of_suffix_take {pattern text : List α} {endOffset : Nat}
    (hend : endOffset ≤ text.length) (hsuffix : pattern.IsSuffix (text.take endOffset)) :
    Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text
      (endOffset - pattern.length) := by
  obtain ⟨head, hhead⟩ := List.suffix_iff_exists_append_eq.mp hsuffix
  have htakeLength : (text.take endOffset).length = endOffset := by
    simp [List.length_take, Nat.min_eq_left hend]
  have hheadLength : head.length + pattern.length = endOffset := by
    rw [← hhead] at htakeLength
    simpa using htakeLength
  have hoffset : endOffset - pattern.length = head.length := by omega
  have htext : text = head ++ pattern ++ text.drop endOffset := by
    calc
      text = text.take endOffset ++ text.drop endOffset :=
        (List.take_append_drop endOffset text).symm
      _ = (head ++ pattern) ++ text.drop endOffset := by rw [hhead]
      _ = head ++ pattern ++ text.drop endOffset := by rw [List.append_assoc]
  rw [Cslib.Algorithms.Lean.StringMatching.MatchAt, hoffset, htext]
  constructor
  · simp
  · simp
private lemma firstEnd_matchAt {pattern text : List α} {endOffset : Nat}
    (hfirst : FirstEnd pattern text endOffset) :
    Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text
        (endOffset - pattern.length) ∧
      ∀ earlier < endOffset - pattern.length,
        ¬Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text earlier := by
  refine ⟨matchAt_of_suffix_take hfirst.1 hfirst.2.1, ?_⟩
  intro earlier hearlier hmatch
  have hsuffix := matchAt_suffix_take_add hmatch
  have hpatternLength := hfirst.2.1.length_le
  have htakeLength : (text.take endOffset).length = endOffset := by
    simp [List.length_take, Nat.min_eq_left hfirst.1]
  have hmle : pattern.length ≤ endOffset := by omega
  exact hfirst.2.2 (earlier + pattern.length) (by omega) hsuffix.2
private theorem timedScan_correct [BEq α] [LawfulBEq α]
    {pattern consumed : List α} {table : Array.PrefixTable α}
    (htable : IsPrefixTable pattern table)
    (offset : Nat) (state : Fin (table.size + 1))
    (hoffset : offset = consumed.length)
    (hstate : state.val ≤ pattern.length ∧
      (pattern.take state.val).IsSuffix consumed ∧
      ∀ k, k ≤ pattern.length → (pattern.take k).IsSuffix consumed → k ≤ state.val)
    (hno : ∀ endOffset, endOffset ≤ consumed.length →
      ¬pattern.IsSuffix (consumed.take endOffset)) (remaining : List α) :
    (∀ start,
      (timedScan table offset state remaining).ret = some start →
        ∃ endOffset, FirstEnd pattern (consumed ++ remaining) endOffset ∧
          start = endOffset - pattern.length) ∧
    ((timedScan table offset state remaining).ret = none →
      ∀ endOffset, endOffset ≤ (consumed ++ remaining).length →
        ¬pattern.IsSuffix ((consumed ++ remaining).take endOffset)) := by
  induction remaining generalizing consumed offset state with
  | nil =>
      rw [timedScan.eq_def]
      constructor
      · intro start h
        simp at h
      · intro _ endOffset hend
        simpa using hno endOffset (by simpa using hend)
  | cons x xs ih =>
      rw [timedScan.eq_def, ret_bind, ret_timedStep]
      let next := table.step x state
      have hnext := step_spec htable x state hstate
      by_cases hfound : next.val = table.size
      · simp only [next, hfound, ite_true, ret_pure]
        constructor
        · intro start hstart
          injection hstart with hstart
          subst start
          refine ⟨consumed.length + 1, ?_, ?_⟩
          · refine ⟨by simp, ?_, ?_⟩
            · have htake :
                  (consumed ++ x :: xs).take (consumed.length + 1) = consumed ++ [x] := by
                rw [show consumed ++ x :: xs = (consumed ++ [x]) ++ xs by simp]
                rw [List.take_append_of_le_length (by simp)]
                have hlength : consumed.length + 1 = (consumed ++ [x]).length := by simp
                rw [hlength, List.take_length]
              have htableSize : table.size = pattern.length := htable.1
              have hnextEq : next.val = pattern.length := by omega
              have htpattern : pattern.take next.val = pattern := by
                rw [hnextEq, List.take_length]
              rw [htake, ← htpattern]
              exact hnext.2.1
            · intro earlier hearlier hsuffix
              have hearlierLe : earlier ≤ consumed.length := by omega
              have htake : (consumed ++ x :: xs).take earlier = consumed.take earlier := by
                exact List.take_append_of_le_length hearlierLe
              exact hno earlier hearlierLe (by simpa [htake] using hsuffix)
          · rw [hoffset, htable.1]
        · intro hnone
          contradiction
      · simp only [next, hfound, ite_false]
        have hnoNext : ∀ endOffset, endOffset ≤ (consumed ++ [x]).length →
            ¬pattern.IsSuffix ((consumed ++ [x]).take endOffset) := by
          intro endOffset hend hsuffix
          by_cases hold : endOffset ≤ consumed.length
          · rw [List.take_append_of_le_length hold] at hsuffix
            exact hno endOffset hold hsuffix
          · have hendEq : endOffset = consumed.length + 1 := by simp at hend; omega
            subst endOffset
            have hfull : (consumed ++ [x]).take (consumed.length + 1) = consumed ++ [x] := by
              have hlength : consumed.length + 1 = (consumed ++ [x]).length := by simp
              rw [hlength, List.take_length]
            rw [hfull] at hsuffix
            have htableSize : table.size = pattern.length := htable.1
            have hmax := hnext.2.2 pattern.length (Nat.le_refl _) (by
              simpa [List.take_length] using hsuffix)
            have hnextLe := hnext.1
            have : next.val = table.size := by omega
            exact hfound this
        have hrec := ih (offset + 1) next (by simp [hoffset]) hnext hnoNext
        simpa only [List.append_assoc, List.singleton_append] using hrec
private theorem timedScan_initial_correct [BEq α] [LawfulBEq α]
    {pattern : List α} (table : Array.PrefixTable α)
    (htable : IsPrefixTable pattern table) (text : List α) (hpattern : pattern ≠ []) :
    (∀ start, (timedScan table 0 0 text).ret = some start →
      ∃ endOffset, FirstEnd pattern text endOffset ∧
        start = endOffset - pattern.length) ∧
    ((timedScan table 0 0 text).ret = none →
      ∀ endOffset, endOffset ≤ text.length →
        ¬pattern.IsSuffix (text.take endOffset)) := by
  have hstate : (0 : Fin (table.size + 1)).val ≤ pattern.length ∧
      (pattern.take (0 : Fin (table.size + 1)).val).IsSuffix [] ∧
      ∀ k, k ≤ pattern.length → (pattern.take k).IsSuffix [] →
        k ≤ (0 : Fin (table.size + 1)).val := by
    refine ⟨by simp, by simp, ?_⟩
    intro k hk hsuffix
    have hlength := hsuffix.length_le
    simp [List.length_take, Nat.min_eq_left hk] at hlength
    omega
  have hno : ∀ endOffset, endOffset ≤ ([] : List α).length →
      ¬pattern.IsSuffix ([].take endOffset) := by
    intro endOffset hend hsuffix
    have hendZero : endOffset = 0 := by simpa using hend
    subst endOffset
    exact hpattern (List.suffix_nil.mp (by simpa using hsuffix))
  simpa using timedScan_correct htable 0 0 rfl hstate hno text
private theorem kmpSearch_cons_correct [BEq α] [LawfulBEq α]
    (head : α) (tail text : List α) :
    (∀ start, (kmpSearch (head :: tail) text).ret = some start →
      ∃ endOffset, FirstEnd (head :: tail) text endOffset ∧
        start = endOffset - (head :: tail).length) ∧
    ((kmpSearch (head :: tail) text).ret = none →
      ∀ endOffset, endOffset ≤ text.length →
        ¬(head :: tail).IsSuffix (text.take endOffset)) := by
  let build := timedBuildFrom (default : Array.PrefixTable α) (head :: tail)
  have htable : IsPrefixTable (head :: tail) build.ret := by
    rw [ret_timedBuild]
    exact isPrefixTable_mkPrefixTable (head :: tail)
  have hscan := timedScan_initial_correct build.ret htable text (by simp)
  simpa [kmpSearch, build] using hscan
private theorem kmpSearch_some_sound [BEq α] [LawfulBEq α]
    (pattern text : List α) (start : Nat)
    (hresult : (kmpSearch pattern text).ret = some start) :
    Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text start ∧
      ∀ earlier < start,
        ¬Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text earlier := by
  cases pattern with
  | nil =>
      simp [kmpSearch] at hresult
      subst start
      simp [Cslib.Algorithms.Lean.StringMatching.MatchAt]
  | cons head tail =>
      obtain ⟨endOffset, hfirst, hstart⟩ :=
        (kmpSearch_cons_correct head tail text).1 start hresult
      have hmatch := firstEnd_matchAt hfirst
      rwa [hstart]
private theorem kmpSearch_none_sound [BEq α] [LawfulBEq α]
    (pattern text : List α) (hresult : (kmpSearch pattern text).ret = none) :
    ∀ offset, ¬Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text offset := by
  cases pattern with
  | nil => simp [kmpSearch] at hresult
  | cons head tail =>
      intro offset hmatch
      have hsuffix := matchAt_suffix_take_add hmatch
      exact (kmpSearch_cons_correct head tail text).2 hresult
        (offset + (head :: tail).length) hsuffix.1 hsuffix.2

/-- KMP returns an offset exactly when it is the least offset matching the pattern. -/
theorem kmpSearch_eq_some_iff [BEq α] [LawfulBEq α]
    (pattern text : List α) (offset : Nat) :
    (kmpSearch pattern text).ret = some offset ↔
      Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text offset ∧
        ∀ earlier < offset,
          ¬Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text earlier := by
  constructor
  · exact kmpSearch_some_sound pattern text offset
  · rintro ⟨hmatch, hleast⟩
    cases hresult : (kmpSearch pattern text).ret with
    | none => exact False.elim (kmpSearch_none_sound pattern text hresult offset hmatch)
    | some found =>
        have hfound := kmpSearch_some_sound pattern text found hresult
        have heq : found = offset := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · exact hleast found hlt hfound.1
          · exact hfound.2 offset hgt hmatch
        subst found
        rfl

/-- KMP returns no offset exactly when no bounded offset matches the pattern. -/
theorem kmpSearch_eq_none_iff [BEq α] [LawfulBEq α]
    (pattern text : List α) :
    (kmpSearch pattern text).ret = none ↔
      ∀ offset, ¬Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text offset := by
  constructor
  · exact kmpSearch_none_sound pattern text
  · intro hnone
    cases hresult : (kmpSearch pattern text).ret with
    | none => rfl
    | some offset =>
        exact False.elim (hnone offset (kmpSearch_some_sound pattern text offset hresult).1)

/-- KMP returns no offset exactly when the pattern is not an infix of the text. -/
theorem kmpSearch_eq_none_iff_not_isInfix [BEq α] [LawfulBEq α]
    (pattern text : List α) :
    (kmpSearch pattern text).ret = none ↔ ¬pattern.IsInfix text := by
  rw [kmpSearch_eq_none_iff]
  constructor
  · intro hnone hinfix
    obtain ⟨offset, hmatch⟩ :=
      (Cslib.Algorithms.Lean.StringMatching.exists_matchAt_iff_isInfix pattern text).mpr hinfix
    exact hnone offset hmatch
  · intro hnot offset hmatch
    exact hnot <|
      (Cslib.Algorithms.Lean.StringMatching.exists_matchAt_iff_isInfix pattern text).mp
        ⟨offset, hmatch⟩

open Cslib.Algorithms.Lean.StringMatching
private theorem dropInfix?_map_length_eq_some_iff [BEq α] [LawfulBEq α]
    (pattern text : List α) (offset : Nat) :
    (List.dropInfix? text pattern).map (fun result => result.1.length) = some offset ↔
      MatchAt pattern text offset ∧
        ∀ earlier < offset, ¬MatchAt pattern text earlier := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨pre, suffix⟩, hdrop, hlength⟩
    obtain ⟨⟨matched, htext, hmatched⟩, hleast⟩ :=
      List.dropInfix?_eq_some_iff.mp hdrop
    rw [beq_iff_eq] at hmatched
    subst matched
    have hmatch : MatchAt pattern text pre.length := by simp [MatchAt, htext]
    subst offset
    refine ⟨hmatch, ?_⟩
    intro earlier hearlier hearlierMatch
    change earlier < pre.length at hearlier
    obtain ⟨rest, hrest⟩ :=
      List.prefix_iff_exists_eq_append.mp hearlierMatch.2
    have hdecomp := (List.take_append_drop earlier text).symm
    rw [hrest, ← List.append_assoc] at hdecomp
    have hprefixLength := hleast (text.take earlier) pattern rest hdecomp
      (beq_iff_eq.mpr rfl)
    have htakeLength : (text.take earlier).length = earlier := by
      simp [List.length_take, Nat.min_eq_left hearlierMatch.1]
    omega
  · rintro ⟨hmatch, hleast⟩
    obtain ⟨suffix, hsuffix⟩ := List.prefix_iff_exists_eq_append.mp hmatch.2
    have hdecomp := (List.take_append_drop offset text).symm
    rw [hsuffix, ← List.append_assoc] at hdecomp
    have hdrop : List.dropInfix? text pattern = some (text.take offset, suffix) := by
      rw [List.dropInfix?_eq_some_iff]
      constructor
      · exact ⟨pattern, hdecomp, beq_iff_eq.mpr rfl⟩
      · intro pre matched rest htext hmatched
        rw [beq_iff_eq] at hmatched
        subst matched
        have hpreMatch : MatchAt pattern text pre.length := by simp [MatchAt, htext]
        have htakeLength : (text.take offset).length = offset := by
          simp [List.length_take, Nat.min_eq_left hmatch.1]
        rw [htakeLength]
        by_contra hnot
        exact hleast pre.length (by omega) hpreMatch
    exact ⟨(text.take offset, suffix), hdrop, by
      simp [List.length_take, Nat.min_eq_left hmatch.1]⟩

/-- For a nonempty pattern, KMP agrees with the start-offset projection of `List.dropInfix?`. -/
theorem kmpSearch_eq_dropInfix?_map_length [BEq α] [LawfulBEq α]
    (pattern text : List α) (hpattern : pattern ≠ []) :
    (kmpSearch pattern text).ret =
      (List.dropInfix? text pattern).map fun result => result.1.length := by
  cases pattern with
  | nil => contradiction
  | cons _ _ =>
      apply Option.ext
      intro offset
      rw [kmpSearch_eq_some_iff, dropInfix?_map_length_eq_some_iff]
private theorem timedStep_time_add_ret_le [BEq α]
    (table : Array.PrefixTable α) (x : α) (state : Fin (table.size + 1)) :
    (timedStep table x state).time +
        (timedStep table x state).ret.val ≤ state.val + 2 := by
  induction hstate : state.val using Nat.strong_induction_on generalizing state with
  | h stateValue ih =>
      obtain ⟨state, hstateSize⟩ := state
      simp only at hstate
      subst stateValue
      rw [timedStep.eq_def]
      by_cases hsize : state < table.size
      · simp only [hsize, ↓reduceDIte, time_bind, time_tick]
        by_cases heq : (x == table.toArray[state].1) = true
        · simp only [heq, ite_true, time_pure, ret_bind, ret_pure]
          omega
        · simp only [heq, Bool.false_eq_true, ↓reduceIte, ret_bind]
          cases state with
          | zero => simp
          | succ q =>
              have hindex : q < table.size := Nat.lt_of_succ_lt_succ hstateSize
              let failure := table.toArray[q].2
              have hfailureLt : failure < q + 1 :=
                Nat.lt_succ_of_le (table.valid hindex)
              change 1 +
                  (timedStep table x
                    ⟨failure, hfailureLt.trans hstateSize⟩).time +
                  (timedStep table x
                    ⟨failure, hfailureLt.trans hstateSize⟩).ret.val ≤ (q + 1) + 2
              have hrec := ih failure hfailureLt
                ⟨failure, hfailureLt.trans hstateSize⟩ rfl
              have hrec' : 1 +
                  (timedStep table x
                    ⟨failure, hfailureLt.trans hstateSize⟩).time +
                  (timedStep table x
                    ⟨failure, hfailureLt.trans hstateSize⟩).ret.val ≤
                  1 + (failure + 2) := by
                simpa only [Nat.add_assoc] using Nat.add_le_add_left hrec 1
              have hbound : 1 + (failure + 2) ≤ (q + 1) + 2 := by omega
              exact Nat.le_trans hrec' hbound
      · simp only [hsize, ↓reduceDIte]
        cases state with
        | zero => simp
        | succ q =>
            have hindex : q < table.size := Nat.lt_of_succ_lt_succ hstateSize
            let failure := table.toArray[q].2
            have hfailureLt : failure < q + 1 :=
              Nat.lt_succ_of_le (table.valid hindex)
            have hrec := ih failure hfailureLt
              ⟨failure, hfailureLt.trans hstateSize⟩ rfl
            exact Nat.le_trans hrec (by omega)
private theorem timedScan_time_le [BEq α] (table : Array.PrefixTable α)
    (offset : Nat) (state : Fin (table.size + 1)) (text : List α) :
    (timedScan table offset state text).time ≤
      2 * text.length + state.val := by
  induction text generalizing offset state with
  | nil => simp [timedScan.eq_def]
  | cons x xs ih =>
      rw [timedScan.eq_def, time_bind, ret_timedStep]
      let next := table.step x state
      have hstep := timedStep_time_add_ret_le table x state
      have hret := congrArg Fin.val (ret_timedStep table x state)
      have hstepNext : (timedStep table x state).time + next.val ≤
          state.val + 2 := by omega
      by_cases hfound : next.val = table.size
      · simp only [next, hfound, ite_true, time_pure, List.length_cons]
        have hnonneg : 0 ≤ next.val := Nat.zero_le _
        omega
      · simp only [next, hfound, ite_false, List.length_cons]
        have hrest := ih (offset + 1) next
        have hsum : (timedStep table x state).time +
              (2 * xs.length + next.val) ≤ 2 * (xs.length + 1) + state.val := by
          omega
        exact Nat.le_trans (Nat.add_le_add_left hrest _) hsum
private def failurePotential (table : Array.PrefixTable α) : Nat :=
  (table.toArray.back?.map Prod.snd).getD 0
private lemma failurePotential_eq_last (table : Array.PrefixTable α)
    (hsize : table.size ≠ 0) :
    failurePotential table = (table.toArray[table.size - 1]'(by
      have hpos := Nat.pos_of_ne_zero hsize
      exact Nat.sub_lt hpos Nat.zero_lt_one)).2 := by
  have hpos := Nat.pos_of_ne_zero hsize
  have hindex : table.size - 1 < table.size := Nat.sub_lt hpos Nat.zero_lt_one
  rw [failurePotential, Array.back?_eq_getElem?, Array.getElem?_eq_getElem hindex]
  rfl
private lemma timedStep_at_size_time_add_ret_le [BEq α]
    (table : Array.PrefixTable α) (x : α) (state : Fin (table.size + 1))
    (hstate : state.val = table.size) :
    (timedStep table x state).time +
        (timedStep table x state).ret.val ≤
      failurePotential table + 2 := by
  obtain ⟨state, hstateSize⟩ := state
  simp only at hstate
  rw [timedStep.eq_def]
  simp only [show ¬state < table.size by omega, ↓reduceDIte]
  cases state with
  | zero =>
      have hsize : table.size = 0 := by omega
      simp [failurePotential, Array.back?_eq_getElem?, hsize]
  | succ q =>
      have hindex : q < table.size := by omega
      let failure := table.toArray[q].2
      have hfailureLt : failure < q + 1 := Nat.lt_succ_of_le (table.valid hindex)
      have hpotential : failurePotential table = failure := by
        rw [failurePotential_eq_last table (by omega)]
        congr 2
        omega
      have hstep := timedStep_time_add_ret_le table x
        ⟨failure, hfailureLt.trans hstateSize⟩
      simpa [hpotential] using hstep

private theorem timedBuild_time_add_potential_le [BEq α]
    (table : Array.PrefixTable α) (xs : List α) :
    (timedBuildFrom table xs).time +
        failurePotential (timedBuildFrom table xs).ret ≤
      failurePotential table + 2 * xs.length := by
  induction xs generalizing table with
  | nil => simp [timedBuildFrom.eq_def]
  | cons x xs ih =>
      rw [timedBuildFrom.eq_def]
      let step := timedStep table x ⟨table.size, Nat.lt_succ_self _⟩
      let nextTable := extendWith table x step.ret
      let rest := timedBuildFrom nextTable xs
      have hstep := timedStep_at_size_time_add_ret_le table x
        ⟨table.size, Nat.lt_succ_self _⟩ rfl
      have hrest := ih nextTable
      have hpotential : failurePotential nextTable = step.ret.val := by
        simp [nextTable, failurePotential, extendWith, Array.back?_push]
      change step.time + rest.time + failurePotential rest.ret ≤
        failurePotential table + 2 * (xs.length + 1)
      dsimp only [step, nextTable, rest] at hrest hpotential ⊢
      omega

private theorem timedBuild_time_le [BEq α] (pattern : List α) :
    (timedBuildFrom (default : Array.PrefixTable α) pattern).time ≤
      2 * pattern.length := by
  have hbound := timedBuild_time_add_potential_le
    (default : Array.PrefixTable α) pattern
  have hdefault : failurePotential (default : Array.PrefixTable α) = 0 := rfl
  omega

/-- KMP uses at most twice the combined pattern and text lengths in symbol comparisons. -/
theorem kmpSearch_time_le [BEq α] (pattern text : List α) :
    (kmpSearch pattern text).time ≤ 2 * pattern.length + 2 * text.length := by
  cases pattern with
  | nil => simp [kmpSearch]
  | cons head tail =>
      rw [kmpSearch]
      dsimp only
      let build := timedBuildFrom (default : Array.PrefixTable α) (head :: tail)
      have hbuild := timedBuild_time_le (α := α) (head :: tail)
      have hscan := timedScan_time_le build.ret 0 0 text
      have hscan' : (timedScan build.ret 0 0 text).time ≤
          2 * text.length := by simpa using hscan
      change build.time + (timedScan build.ret 0 0 text).time ≤
        2 * (head :: tail).length + 2 * text.length
      dsimp only [build] at hscan' ⊢
      omega

end Cslib.Algorithms.Lean.TimeM

namespace Array

universe u

/-- Each failure entry is the longest proper prefix that is also a suffix. -/
theorem mkPrefixTable_failure_spec {α : Type u} [BEq α] [LawfulBEq α]
    (pattern : List α) (q : Nat) (hq : q < pattern.length) :
    let table := mkPrefixTable pattern.toArray
    let failure := (table.toArray[q]'(by
      change q < (mkPrefixTable pattern.toArray).size
      rw [mkPrefixTable_size]
      exact hq)).2
    failure ≤ q ∧
      (pattern.take failure).IsSuffix (pattern.take (q + 1)) ∧
      ∀ k, k ≤ q → (pattern.take k).IsSuffix (pattern.take (q + 1)) → k ≤ failure :=
  Cslib.Algorithms.Lean.TimeM.prefixTable_failure_spec_internal pattern q hq

/-- The KMP transition returns the longest pattern prefix that is a suffix after one symbol. -/
theorem mkPrefixTable_step_spec {α : Type u} [BEq α] [LawfulBEq α]
    (pattern consumed : List α) (x : α)
    (state : Fin ((mkPrefixTable pattern.toArray).size + 1))
    (hstate : state.val ≤ pattern.length ∧
      (pattern.take state.val).IsSuffix consumed ∧
      ∀ k, k ≤ pattern.length → (pattern.take k).IsSuffix consumed → k ≤ state.val) :
    let table := mkPrefixTable pattern.toArray
    let next := table.step x state
    next.val ≤ pattern.length ∧
      (pattern.take next.val).IsSuffix (consumed ++ [x]) ∧
      ∀ k, k ≤ pattern.length →
        (pattern.take k).IsSuffix (consumed ++ [x]) → k ≤ next.val :=
  Cslib.Algorithms.Lean.TimeM.prefixTable_step_spec_internal
    pattern consumed x state hstate

end Array

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u}

/-- The empty pattern occurs at offset zero without any symbol comparisons. -/
@[simp]
theorem kmpSearch_nil_pattern [BEq α] (text : List α) :
    kmpSearch [] text = pure (some 0) := by
  simp [kmpSearch]

end Cslib.Algorithms.Lean.TimeM
