/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance
import all CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm

@[expose] public section

namespace Cslib.Algorithms.Lean.EditDistanceTests

universe u

open Cslib.Algorithms.Lean

example : (editDistance ([] : List Nat) []).ret = ⟨0, []⟩ := by decide
example : (editDistance ([] : List Nat) []).time = ⟨1, 0⟩ := by decide
example : (editDistance ([] : List Nat) [1, 2]).ret =
    ⟨2, [.insert 1, .insert 2]⟩ := by decide
example : (editDistance [1, 2] ([] : List Nat)).ret =
    ⟨2, [.delete 1, .delete 2]⟩ := by decide
example : (editDistance [1, 2] [1, 2]).ret =
    ⟨0, [.keep 1, .keep 2]⟩ := by decide

example : (editDistance [1] [2]).ret = ⟨1, [.substitute 1 2]⟩ := by decide
example : (editDistance [1, 2] [2]).ret = ⟨1, [.delete 1, .keep 2]⟩ := by decide
example : (editDistance [1] [1, 2]).ret = ⟨1, [.keep 1, .insert 2]⟩ := by decide
example : (editDistance ([] : List Nat) [1, 2]).ret.script.apply? [] = some [1, 2] := by decide
example : (editDistance [1, 2] [2]).ret.script.apply? [1, 2] = some [2] := by decide
example : (editDistance [1] [2]).ret.script.apply? [1] = some [2] := by decide
example : (editDistance [1, 2] [2, 1]).ret =
    ⟨2, [.substitute 1 2, .substitute 2 1]⟩ := by decide
example : (editDistance [1, 2, 1] [2, 1, 2]).ret.script =
    [.insert 2, .keep 1, .keep 2, .delete 1] := by decide

example : (editDistance "kitten".toList "sitting".toList).ret =
    ⟨3, [.substitute 'k' 's', .keep 'i', .keep 't', .keep 't',
      .substitute 'e' 'i', .keep 'n', .insert 'g']⟩ := by decide
example : (editDistance "kitten".toList "sitting".toList).ret.script.apply?
    "kitten".toList = some "sitting".toList := by decide
example : (editDistance [1, 1, 2, 1] [1, 2, 2, 1]).ret.distance = 1 := by decide
example : (editDistance [1] [2]).ret.distance <
    EditScript.cost [.delete 1, .insert 2] := by decide

example : EditScript.apply? ([] : EditScript Nat) [1] = none := by decide
example : EditScript.apply? [.keep 1] [] = none := by decide
example : EditScript.apply? [.keep 1] [2] = none := by decide
example : EditScript.apply? [.delete 1] [] = none := by decide
example : EditScript.apply? [.delete 1] [2] = none := by decide
example : EditScript.apply? [.insert 1, .keep 2] [] = none := by decide
example : EditScript.apply? [.substitute 1 2] [] = none := by decide
example : EditScript.apply? [.substitute 1 2] [3] = none := by decide
example : EditScript.apply? [.delete 1, .insert 1] [1] = some [1] := by decide
example : (editDistance [1] [1]).ret.distance ≤
    EditScript.cost [.delete 1, .insert 1] :=
  editDistance_minimal [1] [1] [.delete 1, .insert 1] (by rfl)
example : EditScript.cost ([.keep 1, .substitute 2 3, .insert 4] : EditScript Nat) = 2 :=
  by decide

structure Token where
  value : Nat
  deriving BEq, ReflBEq, LawfulBEq, Repr, DecidableEq

example : (editDistance [Token.mk 1] [Token.mk 1]).ret.distance = 0 := by decide
example : (editDistance [Token.mk 1] [Token.mk 2]).ret.distance = 1 := by decide

example : (editDistance [1, 2, 3] [1, 3]).time = ⟨12, 3⟩ := by decide
example : (editDistance ([] : List Nat) [1, 2]).time = ⟨3, 2⟩ := by decide
example : (editDistance [1, 2] ([] : List Nat)).time = ⟨3, 2⟩ ∧
    (editDistance [1, 2] ([] : List Nat)).time.cellTransitions = 3 ∧
    (editDistance [1, 2] ([] : List Nat)).time.reconstructionSteps = 2 ∧
    (editDistance [1, 2] ([] : List Nat)).time.total = 5 := by decide
example : (editDistance [1, 2] [3, 4]).time = ⟨9, 2⟩ ∧
    (editDistance [1, 2] [3, 4]).time.cellTransitions = 9 ∧
    (editDistance [1, 2] [3, 4]).time.reconstructionSteps = 2 ∧
    (editDistance [1, 2] [3, 4]).time.total = 11 := by decide
example : (editDistance [1, 2] [1, 2]).time = ⟨9, 2⟩ ∧
    (editDistance [1, 2] [1, 2]).time.cellTransitions = 9 ∧
    (editDistance [1, 2] [1, 2]).time.reconstructionSteps = 2 ∧
    (editDistance [1, 2] [1, 2]).time.total = 11 := by decide
example : (editDistance [1, 2] [1, 2]).ret.script.length = 2 ∧
    (editDistance [1, 2] [1, 2]).ret.distance = 0 := by decide

example {α : Type u} [BEq α] [LawfulBEq α] (source target : List α) :
    (editDistance source target).ret.script.Transforms source target :=
  editDistance_script_applies source target
example {α : Type u} [BEq α] (source target : List α) :
    (editDistance source target).ret.script.cost =
      (editDistance source target).ret.distance :=
  editDistance_script_cost source target
example {α : Type u} [BEq α] [LawfulBEq α] (source target : List α)
    (script : EditScript α) (h : script.Transforms source target) :
    (editDistance source target).ret.distance ≤ script.cost :=
  editDistance_minimal source target script h
example {α : Type u} [BEq α] (target : List α) := editDistance_nil_left target
example {α : Type u} [BEq α] (source : List α) := editDistance_nil_right source
example {α : Type u} [BEq α] [LawfulBEq α] (source : List α) := editDistance_self source
example {α : Type u} [BEq α] [LawfulBEq α] (source target : List α) :=
  editDistance_eq_zero_iff source target
example {α : Type u} [BEq α] (source target : List α) :=
  editDistance_cellTransitions source target
example {α : Type u} [BEq α] (source target : List α) :=
  editDistance_reconstructionSteps source target
example {α : Type u} [BEq α] (source target : List α) :=
  editDistance_reconstructionSteps_le source target
example {α : Type u} [BEq α] (source target : List α) := editDistance_time source target

end Cslib.Algorithms.Lean.EditDistanceTests
