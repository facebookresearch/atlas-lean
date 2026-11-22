/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup

/-!
# Tests for the generic group model with deeply embedded programs

Concrete checks at `q = 7` with a shift-by-3 encoding, which moves `0` (so the identity
label differs from the literal label `0`): exponentiation correctness at `m = 0, 1, 5`,
exact static query counts, both outcomes of an equality test, and spot checks of the
transported group laws.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup.Tests

instance : Fact (1 < 7) := ⟨by decide⟩

/-- A concrete encoding on `ZMod 7`: the shift-by-3 permutation. -/
def enc7 : Equiv.Perm (ZMod 7) where
  toFun x := x + 3
  invFun x := x - 3
  left_inv x := add_sub_cancel_right x 3
  right_inv x := sub_add_cancel x 3

theorem enc7_zero : enc7 0 = 3 := by decide

theorem enc7_zero_ne : enc7 0 ≠ 0 := by decide

theorem idLabel_enc7_ne_zero : idLabel enc7 ≠ 0 := by decide

theorem powProg_7_0 :
    enc7 ((0 : ZMod 7) * 2)
      = runProg enc7 (powInputs (idLabel enc7) (enc7 2)) (powProg 0) := by
  decide

theorem powProg_7_1 :
    enc7 ((1 : ZMod 7) * 2)
      = runProg enc7 (powInputs (idLabel enc7) (enc7 2)) (powProg 1) := by
  decide

theorem powProg_7_5 :
    enc7 ((5 : ZMod 7) * 2)
      = runProg enc7 (powInputs (idLabel enc7) (enc7 2)) (powProg 5) := by
  decide

theorem numQueries_7_0 : numQueries (powProg 0) = 0 := by decide

theorem numQueries_7_1 : numQueries (powProg 1) = 1 := by decide

theorem numQueries_7_5 : numQueries (powProg 5) = 5 := by decide

/-- An equality-test program: return input `0` if the inputs agree, else input `1`. -/
def eqTestProg : GProg 2 := .eqTest 0 1 (.ret 0) (.ret 1)

theorem eqTest_true :
    runProg enc7 (powInputs (enc7 2) (enc7 2)) eqTestProg = enc7 2 := by
  decide

theorem eqTest_false :
    runProg enc7 (powInputs (enc7 2) (enc7 5)) eqTestProg = enc7 5 := by
  decide

theorem gmul_spot : gmul enc7 (enc7 2) (enc7 5) = enc7 (2 + 5 : ZMod 7) := by decide

theorem gmul_id_spot : gmul enc7 (enc7 2) (idLabel enc7) = enc7 2 := by decide

theorem ginv_spot : ginv enc7 (enc7 2) = enc7 (-(2 : ZMod 7)) := by decide

theorem gmul_ginv_spot : gmul enc7 (enc7 2) (ginv enc7 (enc7 2)) = idLabel enc7 := by decide

#print axioms run_powProg
#print axioms eval_powProgAux
#print axioms numQueries_powProg
#print axioms length_queriesOf_powProg
#print axioms length_queriesOf_le
#print axioms eval_natural
#print axioms gmul_assoc
#print axioms gmul_id
#print axioms id_gmul
#print axioms gmul_ginv
#print axioms ginv_gmul

end Cslib.Crypto.Framework.GenericGroup.Tests
