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

Concrete checks at `q = 7` with the encoding `Equiv.swap 0 3`, which moves `0` (so the
identity label differs from the literal label `0`): exponentiation correctness at
`m = 0, 1, 5` through the compiler into `OracleComp`, exact query counts and static
bounds, an `eqTest` example, and spot checks of the transported group laws.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup.Tests

instance : Fact (1 < 7) := ⟨by decide⟩

/-- A concrete encoding on `ZMod 7` moving `0`: the transposition `(0 3)`. -/
def enc7 : Equiv.Perm (ZMod 7) := Equiv.swap 0 3

theorem enc7_moves_zero : enc7 0 = 3 := by decide

theorem enc7_zero_ne : enc7 0 ≠ 0 := by decide

theorem idLabel_enc7_ne_zero : idLabel enc7 ≠ 0 := by decide

theorem powProg_7_0 :
    runProg enc7 (powInputs (idLabel enc7) (enc7 2)) (powProg 0)
      = enc7 (0 • (2 : ZMod 7)) := by
  decide

theorem powProg_7_1 :
    runProg enc7 (powInputs (idLabel enc7) (enc7 2)) (powProg 1)
      = enc7 (1 • (2 : ZMod 7)) := by
  decide

theorem powProg_7_5 :
    runProg enc7 (powInputs (idLabel enc7) (enc7 2)) (powProg 5)
      = enc7 (5 • (2 : ZMod 7)) := by
  decide

/-- Behavioral check directly through the compiler and the canonical run. -/
theorem compile_7_5 :
    OracleComp.run (oracleOf enc7)
        (GProg.compile (powInputs (idLabel enc7) (enc7 2)) (powProg 5))
      = enc7 (5 • (2 : ZMod 7)) := by
  decide

theorem queries_7_0 :
    (OracleComp.queries (oracleOf enc7)
      (GProg.compile (powInputs (idLabel enc7) (enc7 2)) (powProg 0))).length = 0 := by
  decide

theorem queries_7_1 :
    (OracleComp.queries (oracleOf enc7)
      (GProg.compile (powInputs (idLabel enc7) (enc7 2)) (powProg 1))).length = 1 := by
  decide

theorem queries_7_5 :
    (OracleComp.queries (oracleOf enc7)
      (GProg.compile (powInputs (idLabel enc7) (enc7 2)) (powProg 5))).length = 5 := by
  decide

theorem numQueries_powProg_5 : numQueries (powProg 5) = 5 := rfl

/-- A tiny branching program: return index `0` if the first two labels agree, else `1`. -/
def eqTestProg : GProg 2 := .eqTest 0 1 (.ret 0) (.ret 1)

theorem eqTest_7_eq :
    runProg enc7 (powInputs (enc7 2) (enc7 2)) eqTestProg = enc7 2 := by
  decide

theorem eqTest_7_ne :
    runProg enc7 (powInputs (enc7 2) (enc7 5)) eqTestProg = enc7 5 := by
  decide

theorem gmul_spot : gmul enc7 (enc7 2) (enc7 5) = enc7 (2 + 5 : ZMod 7) := by decide

theorem gmul_id_spot : gmul enc7 (enc7 2) (idLabel enc7) = enc7 2 := by decide

theorem ginv_spot : ginv enc7 (enc7 2) = enc7 (-(2 : ZMod 7)) := by decide

theorem gmul_ginv_spot : gmul enc7 (enc7 2) (ginv enc7 (enc7 2)) = idLabel enc7 := by decide

#print axioms compile_run
#print axioms isQueryBounded_compile
#print axioms compile_queries
#print axioms run_powProg
#print axioms eval_powProgAux
#print axioms numQueries_powProg
#print axioms eval_natural
#print axioms gmul_assoc
#print axioms gmul_id
#print axioms id_gmul
#print axioms gmul_ginv
#print axioms ginv_gmul

end Cslib.Crypto.Framework.GenericGroup.Tests
