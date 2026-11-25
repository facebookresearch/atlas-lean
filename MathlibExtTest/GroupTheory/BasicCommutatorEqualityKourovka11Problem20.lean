/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BasicCommutatorEqualityKourovka11Problem20
import Mathlib.GroupTheory.FreeGroup.Reduce

namespace MathlibExtTest.GroupTheory.BasicCommutatorEqualityKourovka11Problem20

open MathlibExt.GroupTheory.BasicCommutatorEqualityKourovka11Problem20Wanted

example : ¬ basicCommutatorEqualityDetermines := basicCommutatorEqualityDetermines_refuted

private def weightThenLetterLt (u v : Bracket (Fin 3)) : Prop :=
  u.weight < v.weight ∨
    match u, v with
    | .letter i, .letter j => i < j
    | _, _ => False

-- Hall's condition permits equality with the right entry of the left bracket.
example : (Bracket.comm (.comm (.letter 2) (.letter 0)) (.letter 0)).IsBasic
    weightThenLetterLt := by
  simp only [Bracket.IsBasic, Bracket.weight, weightThenLetterLt]
  decide

-- The condition fails if the right entry of the left bracket is larger.
example : ¬ (Bracket.comm (.comm (.letter 2) (.letter 1)) (.letter 0)).IsBasic
    weightThenLetterLt := by
  simp only [Bracket.IsBasic, Bracket.weight, weightThenLetterLt]
  decide

private def tb : Bracket (Fin 3) := .comm (.letter 1) (.letter 0)

example : tb.eval.toWord = [(1, false), (0, false), (1, true), (0, true)] := by decide

example : (tb.comm (.letter 2)).weight = 3 := rfl

example : (tb.comm (.letter 2)).eval.toWord.length = 10 := by decide

example : tb.eval⁻¹.toWord.length = 4 := by decide

end MathlibExtTest.GroupTheory.BasicCommutatorEqualityKourovka11Problem20
