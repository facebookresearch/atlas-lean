/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.VCG

/-!
# Tests for verification-condition generation

* `x := 0; while x ≤ 2 do x := x + 1` with invariant `x ≤ 3` meets `x = 3`:
  the verification condition is discharged by arithmetic and `vc_valid` gives
  the Hoare triple.
* With the invariant `x = 0` the verification condition is false: the body
  does not preserve it.
* Completeness hands back an annotation of the given command.
-/

@[expose] public section

namespace Cslib.IMP.VCGTests

open ACmd

/-- The loop `while x ≤ 2 do x := x + 1` with invariant `inv`. -/
def countLoop (inv : Assertion) : ACmd :=
  .while inv (.le (.var 0) (.const 2)) (.assign 0 (.add (.var 0) (.const 1)))

/-- `x := 0; while x ≤ 2 do x := x + 1`. -/
def countTo3 (inv : Assertion) : ACmd := .seq (.assign 0 (.const 0)) (countLoop inv)

theorem countTo3_vc : (countTo3 fun s => s 0 ≤ 3).vc (fun s => s 0 = 3) := by
  refine ⟨trivial, ?_, ?_, trivial⟩
  · intro s hinv hguard
    simp only [BExp.eval, AExp.eval] at hguard hinv
    have := of_decide_eq_true hguard
    simp only [ACmd.pre, Assertion.subst, AExp.eval, Function.update_self]
    omega
  · intro s hinv hguard
    simp only [BExp.eval, AExp.eval] at hguard hinv ⊢
    have := of_decide_eq_false hguard
    omega

/-- The triple `{true} x := 0; while x ≤ 2 do x := x + 1 {x = 3}`. -/
example : Valid (fun _ => True) (countTo3 fun s => s 0 ≤ 3).strip (fun s => s 0 = 3) :=
  vc_valid countTo3_vc fun s _ => by
    simp [countTo3, countLoop, ACmd.pre, Assertion.subst]

/-- `x = 0` is not an invariant of the loop body. -/
example : ¬ (countTo3 fun s => s 0 = 0).vc (fun s => s 0 = 3) := by
  rintro ⟨-, hbody, -, -⟩
  have := hbody (fun _ => 0) rfl (by simp [BExp.eval])
  simp [ACmd.pre, Assertion.subst] at this

/-- Completeness produces an annotation of the original command. -/
example : ∃ C : ACmd, C.strip = (countTo3 fun s => s 0 ≤ 3).strip ∧
    C.vc (fun s => s 0 = 3) :=
  let ⟨C, hs, hvc, _⟩ := vc_complete_of_valid (pre' := fun _ => True)
    (vc_valid countTo3_vc fun s _ => by simp [countTo3, countLoop, ACmd.pre, Assertion.subst])
  ⟨C, hs, hvc⟩

end Cslib.IMP.VCGTests
