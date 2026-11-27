/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.IMP.TwoRunProduct

/-! # Regressions for renaming and paired terminating IMP executions -/

set_option autoImplicit false

namespace Cslib.IMP.TwoRunProductTests

private def shift (i : ℕ) : ℕ := i + 3

private theorem shift_injective : Function.Injective shift := by
  intro a b h
  change a + 3 = b + 3 at h
  omega

private def bump : Cmd := .assign 1 (.add (.var 0) (.var 1))

private def input : State := fun i => if i = 3 then 7 else if i = 4 then 5 else 19

private def output : State := Function.update input 4 12

-- A shifted assignment reads both shifted variables and leaves index 2 untouched.
example : BigStep bump (input ∘ shift) (output ∘ shift) ∧ output 2 = 19 := by
  have h : BigStep (bump.rename shift) input output :=
    .assign input 4 (.add (.var 3) (.var 4))
  obtain ⟨hproj, hframe⟩ := (bigStep_rename_iff shift_injective _ _ _).mp h
  have houtside : 2 ∉ Set.range shift := by
    rintro ⟨i, hi⟩
    change i + 3 = 2 at hi
    omega
  exact ⟨hproj, (hframe 2 houtside).trans rfl⟩

private def guard : BExp := .eq (.var 0) (.const 0)

private def loop : Cmd := .while guard (.assign 0 (.const 1))

private def left : State := fun _ => 0

private def right : State := fun _ => 2

private def leftFinal : State := Function.update left 0 1

private theorem left_run : BigStep loop left leftFinal :=
  .whileTrue rfl (.assign left 0 (.const 1)) (.whileFalse rfl)

private theorem right_run : BigStep loop right right := .whileFalse rfl

-- The first copy performs a loop iteration and the second copy performs none.
example : BigStep loop.twoRunProduct (pairStates left right) (pairStates leftFinal right) :=
  (bigStep_twoRunProduct_iff _ _ _ _ _).mp ⟨left_run, right_run⟩

-- The mirrored case requires the odd copy to read its own zero and update it.
example : BigStep loop.twoRunProduct (pairStates right left) (pairStates right leftFinal) :=
  (bigStep_twoRunProduct_iff _ _ _ _ _).mp ⟨right_run, left_run⟩

-- In particular, the second component cannot accidentally see the first component's update.
example :
    ¬ BigStep loop.twoRunProduct (pairStates left right) (pairStates leftFinal leftFinal) := by
  intro h
  have he := BigStep.deterministic right_run ((bigStep_twoRunProduct_iff _ _ _ _ _).mpr h).2
  have h0 := congrFun he 0
  change 2 = 1 at h0
  omega

end Cslib.IMP.TwoRunProductTests
