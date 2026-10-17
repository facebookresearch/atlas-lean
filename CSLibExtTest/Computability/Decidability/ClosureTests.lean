/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Closure

@[expose] public section

/-!
# Tests for closure properties

Boolean combinations and a concatenation, on concrete decidable predicates and languages.
-/

set_option autoImplicit false

open Computability Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability.Closure

/-- Membership of a fixed letter in a word is decidable. -/
theorem tm2Decidable_mem (b : Bool) : TM2Decidable fun w : List Bool ↦ b ∈ w := by
  refine tm2Decidable_iff_computablePred.mpr (ComputablePred.computable_iff.mpr
    ⟨fun w ↦ (w.idxOf b < w.length : Bool), ?_, ?_⟩)
  · exact (Primrec.nat_lt.comp (Primrec.list_idxOf.comp (Primrec.const b) Primrec.id)
      Primrec.list_length).decide.to_comp
  · funext w
    simp [List.idxOf_lt_length_iff]

/-- Words containing both letters. -/
example : TM2Decidable fun w : List Bool ↦ true ∈ w ∧ false ∈ w :=
  (tm2Decidable_mem true).and (tm2Decidable_mem false)

/-- Words containing some letter. -/
example : TM2Decidable fun w : List Bool ↦ true ∈ w ∨ false ∈ w :=
  (tm2Decidable_mem true).or (tm2Decidable_mem false)

/-- Recognizable closure, from decidable inputs. -/
example : TM2Recognizable fun w : List Bool ↦ true ∈ w ∨ false ∈ w :=
  (tm2Decidable_mem true).tm2Recognizable.or (tm2Decidable_mem false).tm2Recognizable

example : TM2Recognizable fun w : List Bool ↦ true ∈ w ∧ false ∈ w :=
  (tm2Decidable_mem true).tm2Recognizable.and (tm2Decidable_mem false).tm2Recognizable

/-- Words containing `true`, and words containing `false`. -/
def hasTrue : Language Bool := {w | true ∈ w}

/-- Words containing `false`. -/
def hasFalse : Language Bool := {w | false ∈ w}

/-- A word containing `true`, followed by a word containing `false`. -/
example : TM2Decidable (· ∈ hasTrue * hasFalse) :=
  (tm2Decidable_mem true).mul (tm2Decidable_mem false)

/-- The split test finds the split of `[true, false]`. -/
example : splitTest (fun u : List Bool ↦ u == [true]) (fun v ↦ v == [false]) [true, false] 3 =
    true := by
  decide

/-- Concatenation of recognizable languages. -/
example : TM2Recognizable (· ∈ hasTrue * hasFalse) :=
  (tm2Decidable_mem true).tm2Recognizable.mul (tm2Decidable_mem false).tm2Recognizable

/-- Kleene star of a decidable language, and of a recognizable one. -/
example : TM2Decidable (· ∈ hasTrue∗) := (tm2Decidable_mem true).kstar

example : TM2Recognizable (· ∈ hasTrue∗) := (tm2Decidable_mem true).tm2Recognizable.kstar

/-- The partitions of a two-letter word. -/
example : partitions [true, false] = [[[true], [false]], [[true, false]]] := by decide

/-- The one-letter words. -/
def oneLetter : Language Bool := {u | u.length = 1}

/-- Every word is in the star of the one-letter words. -/
example (w : List Bool) : w ∈ oneLetter∗ :=
  Language.mem_kstar.mpr ⟨w.map ([·]), by
      induction w with
      | nil => rfl
      | cons a w ih => exact congrArg (a :: ·) ih, fun u hu ↦ by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    rfl⟩

/-- The image of a recognizable language under an alphabet map is recognizable. -/
example : TM2Recognizable (· ∈ Language.map (fun _ : Bool ↦ ()) hasTrue) :=
  (tm2Decidable_mem true).tm2Recognizable.map (Primrec.const ())

end CSLibExtTest.Computability.Decidability.Closure
