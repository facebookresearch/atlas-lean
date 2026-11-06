/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMatrixProjection
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFiber
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRawPacket

/-! The complete matrix constituent of each genuine fifth root normalizing word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exact physical diagonal of the genuine fifth starting matrix constituent. -/
def generatedAxisGlobalFifthMatrixDiagonal (i : Fin 24) : ℝ :=
  if Nat.testBit 0x0f000f i.val then 1 / 2 else 1 / 4

/-- Every chosen phase-preserving fiber root word has the already checked genuine Co1 projection. -/
theorem generatedAxisGlobalFifthShortFiber_matrix_projection (k : Fin 14) :
    projH (QuotientGroup.mk (generatedAxisGlobalFifthShortWordFiber k) : H) =
      QuotientGroup.mk (generatedAxisGlobalFifthShortSpatialWord k) := by
  change projH (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber k)) = _
  rw [generatedAxisGlobalFifthShortWordFiber_local]
  exact generatedAxisGlobalFifthShortLocalWord_projection k

/-- The whole actual Griess matrix output is exactly the genuine spatial matrix action. -/
theorem generatedAxisGlobalFifthShortWord_matrix (k : Fin 14) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis)).1 =
        conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord k)
          (Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal) := by
  rw [generatedAxisGlobalFifthShortWordFiber_encode, generatedAxisGlobalRaw_matrix_projection,
    generatedAxisGlobalFifthShortFiber_matrix_projection, generatedAxisGlobalCo1MatrixAction_mk]
  rw [generatedFifth_matrix]
  rfl

/-- Each actual root matrix entry is an exact twenty-four-coordinate pairing. -/
theorem generatedAxisGlobalFifthShortWord_matrix_entry (k : Fin 14) (i j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis)).1 i j =
        ∑ t : Fin 24, generatedAxisGlobalFifthMatrixDiagonal t *
          (generatedAxisGlobalFifthShortSpatialWord k).val.symm (Pi.single i 1) t *
          (generatedAxisGlobalFifthShortSpatialWord k).val.symm (Pi.single j 1) t := by
  rw [generatedAxisGlobalFifthShortWord_matrix]
  let e := generatedAxisGlobalFifthShortSpatialWord k
  let A := Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal
  calc
    _ = Matrix.toBilin' (conwayMatrixAction e A) (Pi.single i 1) (Pi.single j 1) :=
      (Matrix.toBilin'_single (conwayMatrixAction e A) i j).symm
    _ = Matrix.toBilin' A (e.val.symm (Pi.single i 1))
        (e.val.symm (Pi.single j 1)) := conwayMatrixAction_pairing e A _ _
    _ = _ := by
      simp only [A, Matrix.toBilin'_apply, Matrix.diagonal_apply]
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro t _
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
