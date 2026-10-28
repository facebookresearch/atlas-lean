/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleWordSteps
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreduciblePowerSteps

/-! A checked rank-one operator formed from genuine binary Conway generator matrices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Recorded powers zero through fourteen of the actual word matrix. -/
def co1IrreduciblePowerStage (n : Fin 15) : Fin 29 :=
  if n.val = 0 then 0 else ⟨n.val + 11, by omega⟩

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- The initial recorded matrix is identity. -/
theorem co1Irreducible_stage_zero : co1IrreducibleStage 0 = 1 := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- The recorded projector is the actual sum of the first fifteen word powers. -/
theorem co1Irreducible_projector_sum : ∀ i j : Fin 24,
    (∑ n : Fin 15, co1IrreducibleStage (co1IrreduciblePowerStage n)) i j =
      co1IrreducibleStage 26 i j := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- The intermediate matrix is the actual Xi generator times the projector. -/
theorem co1Irreducible_projector_middle : ∀ i j : Fin 24,
    (omegaOrbitBinaryMatrices 0 * co1IrreducibleStage 26) i j =
      co1IrreducibleStage 27 i j := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- The final matrix is the actual projector-Xi-projector composition. -/
theorem co1Irreducible_projector_product : ∀ i j : Fin 24,
    (co1IrreducibleStage 26 * co1IrreducibleStage 27) i j =
      co1IrreducibleStage 28 i j := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- The genuine composition is exactly the displayed nonzero rank-one outer product. -/
theorem co1Irreducible_rank_one : ∀ i j : Fin 24,
    co1IrreducibleStage 28 i j = co1IrreducibleColumn i * co1IrreducibleRow j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
