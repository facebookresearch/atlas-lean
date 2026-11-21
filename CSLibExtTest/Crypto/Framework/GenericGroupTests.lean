/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup

/-!
# Tests for the generic group model over `OracleComp`

Concrete checks at `q = 7` with the encoding `Equiv.swap 0 3`, which moves `0` (so the
identity label differs from the literal label `0`): exponentiation correctness at
`n = 0, 1, 5`, exact query counts, and spot checks of the transported group laws.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup.Tests

/-- A concrete encoding on `ZMod 7` moving `0`: the transposition `(0 3)`. -/
def enc7 : Equiv.Perm (ZMod 7) := Equiv.swap 0 3

theorem enc7_moves_zero : enc7 0 = 3 := by decide

theorem enc7_zero_ne : enc7 0 ≠ 0 := by decide

theorem idLabel_enc7_ne_zero : idLabel enc7 ≠ 0 := by decide

theorem powProg_7_0 :
    runProg enc7 (powProg 0 (idLabel enc7) (enc7 2)) = enc7 (0 • (2 : ZMod 7)) := by
  decide

theorem powProg_7_1 :
    runProg enc7 (powProg 1 (idLabel enc7) (enc7 2)) = enc7 (1 • (2 : ZMod 7)) := by
  decide

theorem powProg_7_5 :
    runProg enc7 (powProg 5 (idLabel enc7) (enc7 2)) = enc7 (5 • (2 : ZMod 7)) := by
  decide

theorem queries_7_0 :
    (OracleComp.queries (oracleOf enc7) (powProg 0 (idLabel enc7) (enc7 2))).length = 0 := by
  decide

theorem queries_7_1 :
    (OracleComp.queries (oracleOf enc7) (powProg 1 (idLabel enc7) (enc7 2))).length = 1 := by
  decide

theorem queries_7_5 :
    (OracleComp.queries (oracleOf enc7) (powProg 5 (idLabel enc7) (enc7 2))).length = 5 := by
  decide

theorem gmul_spot : gmul enc7 (enc7 2) (enc7 5) = enc7 (2 + 5 : ZMod 7) := by decide

theorem gmul_id_spot : gmul enc7 (enc7 2) (idLabel enc7) = enc7 2 := by decide

theorem ginv_spot : ginv enc7 (enc7 2) = enc7 (-(2 : ZMod 7)) := by decide

theorem gmul_ginv_spot : gmul enc7 (enc7 2) (ginv enc7 (enc7 2)) = idLabel enc7 := by decide

#print axioms run_powProg
#print axioms run_powProg_core
#print axioms queries_powProg_length
#print axioms isQueryBounded_powProg
#print axioms gmul_assoc
#print axioms gmul_id
#print axioms id_gmul
#print axioms gmul_ginv
#print axioms ginv_gmul

end Cslib.Crypto.Framework.GenericGroup.Tests
