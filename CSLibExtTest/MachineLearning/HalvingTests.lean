/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Halving

/-!
# Halving algorithm tests

Concrete runs over the domain `Bool`, checked by evaluation:
* `C` has the four distinct concepts `id`, `not`, `const true` and `const false`. On the sequence
  `[(false, true), (true, true)]`, labeled by `const true`, both predictions are ties of the version
  space, so halving predicts `false` and errs twice: the version space shrinks `4 → 2 → 1`, and the
  bound `2 ^ 2 ≤ 4` is tight.
* `C'` has the three concepts `id`, `const true` and `const false`. On `[(true, false),
  (false, false)]`, labeled by `const false`, the majority predicts `true` at `true` (a mistake
  that leaves one concept) and then `false` at `false` (a correct prediction), so halving errs
  once.
-/

@[expose] public section

namespace Cslib.MachineLearning.HalvingTests

open Cslib.MachineLearning.Halving

/-- The four Boolean functions of one Boolean variable. -/
def C : Finset (Bool → Bool) := {id, not, fun _ => true, fun _ => false}

/-- The examples `(false, true), (true, true)`, labeled by `const true`. -/
def S : List (Bool × Bool) := [(false, true), (true, true)]

example : C.card = 4 := by decide

/-- First round: `not` and `const true` say `true`, `id` and `const false` say `false`; the tie is
predicted `false`, but the label is `true`. -/
example : countTrue C [] false = 2 ∧ halvingPredict C [] false = false := by decide

/-- The mistake halves the version space to `{not, const true}`. -/
example : versionSpace C [(false, true)] = {not, fun _ => true} := by decide

example : (versionSpace C [(false, true)]).card = 2 := by decide

example : 2 * (versionSpace C ([] ++ [(false, true)])).card ≤ (versionSpace C []).card :=
  versionSpace_card_le_of_mistake C [] false true (by decide)

/-- Second round: one of `not, const true` says `true` at `true`; the tie is predicted `false`, a
second mistake, which leaves only `const true`. -/
example : countTrue C [(false, true)] true = 1 ∧
    halvingPredict C [(false, true)] true = false := by decide

example : (versionSpace C S).card = 1 := by decide

example : halvingMistakes C [] S = 2 := by decide

/-- The bound for this run, `2 ^ 2 ≤ 4`, through the theorem. -/
example : 2 ^ halvingMistakes C [] S ≤ C.card :=
  halving_mistakes_bound C S ⟨fun _ => true, by decide, by decide⟩

/-- `id`, `const true` and `const false`. -/
def C' : Finset (Bool → Bool) := {id, fun _ => true, fun _ => false}

/-- The examples `(true, false), (false, false)`, labeled by `const false`. -/
def S' : List (Bool × Bool) := [(true, false), (false, false)]

example : C'.card = 3 := by decide

/-- First round: two of three concepts say `true` at `true`, so halving predicts `true`; the label
is `false`. -/
example : countTrue C' [] true = 2 ∧ halvingPredict C' [] true = true := by decide

example : (versionSpace C' [(true, false)]).card = 1 := by decide

/-- Second round: the remaining concept `const false` gives the correct prediction `false`. -/
example : halvingPredict C' [(true, false)] false = false := by decide

example : halvingMistakes C' [] S' = 1 := by decide

example : 2 ^ halvingMistakes C' [] S' ≤ C'.card :=
  halving_mistakes_bound C' S' ⟨fun _ => false, by decide, by decide⟩

end Cslib.MachineLearning.HalvingTests
