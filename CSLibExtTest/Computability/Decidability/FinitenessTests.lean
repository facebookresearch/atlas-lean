/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Finiteness

@[expose] public section

/-!
# Tests for finiteness of the language of a program
-/

set_option autoImplicit false

open Cslib.Decidability
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.Finiteness

/-- `FIN` is neither recognizable nor co-recognizable, hence undecidable. -/
example : ¬TM2Recognizable FiniteCode ∧ ¬TM2CoRecognizable FiniteCode ∧
    ¬TM2Decidable FiniteCode :=
  ⟨not_tm2Recognizable_finite, not_tm2CoRecognizable_finite, not_tm2Decidable_finite⟩

/-- A code defined nowhere has a finite domain. -/
example : ∃ e : Code, FiniteCode e := by
  obtain ⟨e, he⟩ := exists_code_empty
  exact ⟨e, Set.finite_empty.subset fun n hn ↦ by simp [he] at hn⟩

/-- The identity has an infinite domain. -/
example : ¬FiniteCode Code.id := by
  intro h
  refine Set.infinite_univ (h.subset fun n _ ↦ ?_)
  simp [Code.eval_id]

/-- `haltsWithinFun` on the identity: undefined at step bound `0`, defined at `1`. -/
example : haltsWithinFun Code.id 0 = Part.none := by simp [haltsWithinFun, Code.evaln]

example : haltsWithinFun Code.id 1 = Part.some 0 := by
  simp [haltsWithinFun, Code.evaln, Code.id, Seq.seq]

/-- The characteristic lemmas: on the identity, `untilHaltsFun` is defined at step bound `0` and
`haltsWithinFun` is not. -/
example : (untilHaltsFun Code.id 0).Dom ∧ ¬(haltsWithinFun Code.id 0).Dom := by
  simp [untilHaltsFun_dom, haltsWithinFun_dom, Code.evaln]

end CSLibExtTest.Computability.Decidability.Finiteness
