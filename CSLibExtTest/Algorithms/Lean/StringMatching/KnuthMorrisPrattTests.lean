/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.Basic
public meta import CSLibExt.Algorithms.Lean.StringMatching.KnuthMorrisPratt

@[expose] public section

open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.TimeM

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check kmpSearch.timedStep

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check kmpSearch.timedBuildFrom

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check kmpSearch.timedScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check timedStep

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check timedBuildFrom

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check timedScan

private inductive Token where
  | a
  | b
  deriving DecidableEq

private theorem prefixFailure_eq (pattern : List Nat) (q expected : Nat)
    (hq : q < pattern.length) (hexpectedLe : expected ≤ q)
    (hexpectedSuffix : (pattern.take expected).IsSuffix (pattern.take (q + 1)))
    (hexpectedMax : ∀ k, k ≤ q →
      (pattern.take k).IsSuffix (pattern.take (q + 1)) → k ≤ expected) :
    ((Array.mkPrefixTable pattern.toArray).toArray[q]'(by
      change q < (Array.mkPrefixTable pattern.toArray).size
      rw [Array.mkPrefixTable_size]
      exact hq)).2 = expected := by
  have hspec := Array.mkPrefixTable_failure_spec pattern q hq
  let actual := ((Array.mkPrefixTable pattern.toArray).toArray[q]'(by
    change q < (Array.mkPrefixTable pattern.toArray).size
    rw [Array.mkPrefixTable_size]
    exact hq)).2
  change actual = expected
  have hexpectedActual := hspec.2.2 expected hexpectedLe hexpectedSuffix
  have hactualExpected := hexpectedMax actual hspec.1 hspec.2.1
  omega

private theorem false_of_not_suffix {xs ys : List Nat} (hnot : ¬xs.IsSuffix ys)
    (h : xs.IsSuffix ys) : False := hnot h

example : (Array.mkPrefixTable ([0, 0, 0, 0].toArray)).toArray[0].2 = 0 := by
  apply prefixFailure_eq [0, 0, 0, 0] 0 0 (by decide) (by omega) (by decide)
  intro k hk _
  omega

example : (Array.mkPrefixTable ([0, 0, 0, 0].toArray)).toArray[1].2 = 1 := by
  apply prefixFailure_eq [0, 0, 0, 0] 1 1 (by decide) (by omega) (by decide)
  intro k hk _
  omega

example : (Array.mkPrefixTable ([0, 0, 0, 0].toArray)).toArray[2].2 = 2 := by
  apply prefixFailure_eq [0, 0, 0, 0] 2 2 (by decide) (by omega) (by decide)
  intro k hk _
  omega

example : (Array.mkPrefixTable ([0, 0, 0, 0].toArray)).toArray[3].2 = 3 := by
  apply prefixFailure_eq [0, 0, 0, 0] 3 3 (by decide) (by omega) (by decide)
  intro k hk _
  omega

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[0].2 = 0 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 0 0 (by decide) (by omega) (by decide)
  intro k hk _
  omega

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[1].2 = 0 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 1 0 (by decide) (by omega) (by decide)
  intro k hk hsuffix
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · omega
  · exact (false_of_not_suffix (by decide) hsuffix).elim

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[2].2 = 1 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 2 1 (by decide) (by omega) (by decide)
  intro k hk hsuffix
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl
  · omega
  · omega
  · exact (false_of_not_suffix (by decide) hsuffix).elim

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[3].2 = 2 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 3 2 (by decide) (by omega) (by decide)
  intro k hk hsuffix
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · exact (false_of_not_suffix (by decide) hsuffix).elim

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[4].2 = 3 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 4 3 (by decide) (by omega) (by decide)
  intro k hk hsuffix
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · exact (false_of_not_suffix (by decide) hsuffix).elim

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[5].2 = 0 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 5 0 (by decide) (by omega) (by decide)
  intro k hk hsuffix
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  all_goals exact (false_of_not_suffix (by decide) hsuffix).elim

example : (Array.mkPrefixTable ([0, 1, 0, 1, 0, 2, 0].toArray)).toArray[6].2 = 1 := by
  apply prefixFailure_eq [0, 1, 0, 1, 0, 2, 0] 6 1 (by decide) (by omega) (by decide)
  intro k hk hsuffix
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  all_goals exact (false_of_not_suffix (by decide) hsuffix).elim

example : MatchAt ([] : List Nat) [] 0 := by simp [MatchAt]
example : MatchAt ([] : List Nat) [1, 2] 2 := by simp [MatchAt]
example : ¬MatchAt ([] : List Nat) [1, 2] 3 := by simp [MatchAt]
example : MatchAt [1, 2] [0, 1, 2, 1, 2] 1 := by simp [MatchAt]
example : ¬MatchAt [1, 2] [0, 1, 3] 1 := by simp [MatchAt]
example : ¬MatchAt [1, 2, 3] [1, 2] 0 := by simp [MatchAt]

example : ∃ offset, MatchAt [1, 2] [0, 1, 2, 3] offset := by
  rw [exists_matchAt_iff_isInfix]
  decide

example : ¬∃ offset, MatchAt [1, 3] [0, 1, 2, 3] offset := by
  rw [exists_matchAt_iff_isInfix]
  decide

example : (kmpSearch ([] : List Nat) []).ret = some 0 := by
  simp only [kmpSearch_nil_pattern, ret_pure]

example : (kmpSearch ([] : List Nat) [1, 2, 3]).time = 0 := by
  simp only [kmpSearch_nil_pattern, time_pure]

example : (kmpSearch [1, 2] ([] : List Nat)).ret = none := by
  rw [kmpSearch_eq_none_iff]
  simp [MatchAt]

example : (kmpSearch [1, 2] [0, 1, 2, 1, 2]).ret = some 1 := by
  rw [kmpSearch_eq_some_iff]
  simp [MatchAt]

example : (kmpSearch [1, 2, 3] [1, 2, 3]).ret = some 0 := by
  rw [kmpSearch_eq_some_iff]
  simp [MatchAt]

example : (kmpSearch [1, 2, 3] [1, 2]).ret = none := by
  rw [kmpSearch_eq_none_iff]
  intro offset hmatch
  have hlength := hmatch.2.length_le
  simp [List.length_drop] at hlength
  omega

example : (kmpSearch [0, 1, 0, 1, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0]).ret =
    some 2 := by
  rw [kmpSearch_eq_some_iff]
  constructor
  · simp [MatchAt]
  · intro earlier hearlier
    have : earlier = 0 ∨ earlier = 1 := by omega
    rcases this with rfl | rfl <;> simp [MatchAt]

example : (kmpSearch [0, 0, 0] [0, 0, 0, 0, 0]).ret = some 0 := by
  rw [kmpSearch_eq_some_iff]
  simp [MatchAt]

example : (kmpSearch [0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 0]).ret = none := by
  rw [kmpSearch_eq_none_iff]
  intro offset hmatch
  have hlength := hmatch.2.length_le
  simp [List.length_drop] at hlength
  have hoffset : offset = 0 := by omega
  subst offset
  simp [MatchAt] at hmatch

example : (kmpSearch [Token.a, Token.b] [Token.b, Token.a, Token.b]).ret = some 1 := by
  rw [kmpSearch_eq_some_iff]
  simp [MatchAt]

example :
    (kmpSearch [0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 0]).time ≤ 24 := by
  exact kmpSearch_time_le _ _

#guard
  (kmpSearch [0, 1, 0, 1, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0]).time == 18

#guard (kmpSearch [0, 0, 0] [0, 0, 0, 0, 0]).time == 5

#guard (kmpSearch [0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 0]).time == 16

universe u

example {α : Type u} [BEq α] [LawfulBEq α] (pattern : List α) (q : Nat)
    (hq : q < pattern.length) :
    let table := Array.mkPrefixTable pattern.toArray
    let failure := (table.toArray[q]'(by
      change q < (Array.mkPrefixTable pattern.toArray).size
      rw [Array.mkPrefixTable_size]
      exact hq)).2
    failure ≤ q ∧
      (pattern.take failure).IsSuffix (pattern.take (q + 1)) ∧
      ∀ k, k ≤ q → (pattern.take k).IsSuffix (pattern.take (q + 1)) → k ≤ failure :=
  Array.mkPrefixTable_failure_spec pattern q hq

example {α : Type u} [BEq α] [LawfulBEq α] (pattern consumed : List α) (x : α)
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
  Array.mkPrefixTable_step_spec pattern consumed x state hstate

example {α : Type u} [BEq α] [LawfulBEq α] (pattern text : List α) (offset : Nat) :
    (kmpSearch pattern text).ret = some offset ↔
      MatchAt pattern text offset ∧ ∀ earlier < offset, ¬MatchAt pattern text earlier :=
  kmpSearch_eq_some_iff pattern text offset

example {α : Type u} [BEq α] [LawfulBEq α] (pattern text : List α) :
    (kmpSearch pattern text).ret = none ↔ ∀ offset, ¬MatchAt pattern text offset :=
  kmpSearch_eq_none_iff pattern text

example {α : Type u} [BEq α] [LawfulBEq α] (pattern text : List α) :
    (kmpSearch pattern text).ret = none ↔ ¬pattern.IsInfix text :=
  kmpSearch_eq_none_iff_not_isInfix pattern text

example {α : Type u} [BEq α] [LawfulBEq α] (pattern text : List α)
    (hpattern : pattern ≠ []) :
    (kmpSearch pattern text).ret =
      (List.dropInfix? text pattern).map fun result => result.1.length :=
  kmpSearch_eq_dropInfix?_map_length pattern text hpattern

example :
    (kmpSearch [1, 2] [0, 1, 2, 1, 2]).ret =
      (List.dropInfix? [0, 1, 2, 1, 2] [1, 2]).map fun result => result.1.length := by
  apply kmpSearch_eq_dropInfix?_map_length
  decide

example {α : Type u} [BEq α] (pattern text : List α) :
    (kmpSearch pattern text).time ≤ 2 * pattern.length + 2 * text.length :=
  kmpSearch_time_le pattern text
