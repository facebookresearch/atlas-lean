/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskData

/-! Ordinary-kernel certificates for the original binary lifting obstruction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 4000

set_option maxHeartbeats 0 in
-- Ordinary kernel evaluation checks the complete finite source-word data.
/-- Each selected original word returns every coordinate basis vector exactly. -/
theorem co1NonsplitRelation_mask_base (r : Fin 14) :
    ∀ i : Fin 24,
      (co1NonsplitMaskRun (co1NonsplitRelationWords r) (2 ^ i.val, (0, 0))).1 =
        2 ^ i.val := by
  fin_cases r <;> decide +kernel

set_option maxHeartbeats 0 in
-- Ordinary kernel evaluation checks the complete finite source-word data.
/-- Each selected central equation retains all 120 literal correction coordinates. -/
theorem co1NonsplitEquation_mask_state (j : Fin 28) :
    (co1NonsplitMaskRun (co1NonsplitRelationWords (co1NonsplitEquationInput j).1)
      (2 ^ (co1NonsplitEquationInput j).2.val, (0, 0))).2 =
        ((co1NonsplitEquationMasks j).2, (co1NonsplitEquationMasks j).1) := by
  fin_cases j <;> decide +kernel

/-- The selected correction rows sum to zero by exact bitwise XOR. -/
theorem co1NonsplitEquation_rows_xor :
    monsterCo1GeometryBinaryMaskSum
      (List.ofFn (fun j : Fin 28 => (co1NonsplitEquationMasks j).1)) = 0 := by
  decide +kernel

/-- The same selected constant bits sum to one by exact bitwise XOR. -/
theorem co1NonsplitEquation_constants_xor :
    monsterCo1GeometryBinaryMaskSum
      (List.ofFn (fun j : Fin 28 => (co1NonsplitEquationMasks j).2)) = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
