/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleData

/-! Actual cyclic vector and covector bases for the binary Conway representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The twenty-four recorded cyclic vector columns. -/
def co1IrreducibleColumnMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  co1IrreducibleBitMatrix co1IrreducibleColumnRows

/-- The inverse of the recorded cyclic vector matrix. -/
def co1IrreducibleColumnInverse : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  co1IrreducibleBitMatrix co1IrreducibleColumnInverseRows

/-- The twenty-four recorded cyclic functional rows. -/
def co1IrreducibleRowMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  co1IrreducibleBitMatrix co1IrreducibleRowRows

/-- The inverse of the recorded cyclic functional matrix. -/
def co1IrreducibleRowInverse : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  co1IrreducibleBitMatrix co1IrreducibleRowInverseRows

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- Both basis matrices have the displayed genuine inverses. -/
theorem co1Irreducible_basis_inverses :
    co1IrreducibleColumnMatrix * co1IrreducibleColumnInverse = 1 ∧
      co1IrreducibleRowInverse * co1IrreducibleRowMatrix = 1 := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- Both cyclic basis trees start at their genuine rank-one vector and functional. -/
theorem co1Irreducible_cyclic_starts :
    co1IrreducibleColumnMatrix.col 0 = co1IrreducibleColumn ∧
      co1IrreducibleRowMatrix.row 0 = co1IrreducibleRow := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- Every later basis vector has an earlier recorded parent. -/
theorem co1Irreducible_cyclic_parents : ∀ j : Fin 24, j ≠ 0 →
    (co1IrreducibleColumnParents j).val < j.val ∧
      (co1IrreducibleRowParents j).val < j.val := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- Each recorded column is the image of its parent under a genuine generator. -/
theorem co1Irreducible_cyclic_columns : ∀ j : Fin 24, j ≠ 0 →
    omegaOrbitBinaryMatrices (co1IrreducibleColumnLetters j) *ᵥ
      co1IrreducibleColumnMatrix.col (co1IrreducibleColumnParents j) =
        co1IrreducibleColumnMatrix.col j := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- Each recorded row is its parent functional followed by a genuine generator. -/
theorem co1Irreducible_cyclic_rows : ∀ j : Fin 24, j ≠ 0 →
    co1IrreducibleRowMatrix.row (co1IrreducibleRowParents j) ᵥ*
      omegaOrbitBinaryMatrices (co1IrreducibleRowLetters j) =
        co1IrreducibleRowMatrix.row j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
