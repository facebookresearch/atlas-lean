/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskBindings

/-! Exact decoding of the original binary matrices and their central cochains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

/-- The exact XOR evaluator is the full action of the original binary matrix. -/
theorem co1NonsplitMaskVector_decode (k : Fin 5) (v : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskVector k v) =
      omegaOrbitBinaryMatrices k *ᵥ monsterCo1GeometryBinaryMaskDecode v := by
  unfold co1NonsplitMaskVector
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases hv : v.testBit j.val
  · simp [monsterCo1GeometryBinaryMaskDecode, hv]
  · simpa [monsterCo1GeometryBinaryMaskDecode, hv] using
      co1NonsplitColumnMasks_decode k i j

/-- Evaluating the phase masks is the literal quadratic polynomial of their matrix. -/
theorem co1NonsplitMaskPhase_decode (k : Fin 5) (v : ℕ) :
    (if (co1NonsplitMaskPhase k v).testBit 0 then (1 : ZMod 2) else 0) =
      ∑ i : Fin 24, ∑ j : Fin 24,
        monsterCo1GeometryBinaryMaskDecode v i *
          monsterCo1GeometryBinaryMaskDecode (co1NonsplitPhaseMasks k i) j *
            monsterCo1GeometryBinaryMaskDecode v j := by
  unfold co1NonsplitMaskPhase
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases hv : v.testBit i.val
  · simp [monsterCo1GeometryBinaryMaskDecode, hv]
  · simpa [monsterCo1GeometryBinaryMaskDecode, hv] using
      monsterCo1GeometryBinaryMaskDot_decode 24 (co1NonsplitPhaseMasks k i) v

/-- Each original quotient generator acts by the certified matrix. -/
theorem co1NonsplitFive_action (k : Fin 5) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (monsterCo1FiveGenerator k) v = omegaOrbitBinaryMatrices k *ᵥ v := by
  rw [← monsterCo1GeometryVectorFiveOperator_actual,
    monsterCo1GeometryTransportOperator_binary,
    monsterCo1GeometryVectorFiveOperator_matrix]

/-- The actual original action on a unit is the complete decoded column. -/
theorem co1NonsplitFive_unit (k : Fin 5) (i : Fin 24) :
    co1BinaryAction (monsterCo1FiveGenerator k) (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (co1NonsplitColumnMasks k i) := by
  rw [co1NonsplitFive_action]
  ext j
  simp only [Matrix.mulVec, dotProduct_single_one]
  exact (co1NonsplitColumnMasks_decode k j i).symm

/-- The stored phase matrix is the actual canonical cochain matrix. -/
theorem co1NonsplitFive_correction_matrix (k : Fin 5) :
    qCorrectionMatrix (co1BinaryAction (monsterCo1FiveGenerator k)) =
      monsterCo1GeometryBinaryMaskMatrix (co1NonsplitPhaseMasks k) := by
  ext i j
  rw [qCorrectionMatrix, qCocycleDifference_apply, co1NonsplitFive_unit,
    co1NonsplitFive_unit]
  exact (co1NonsplitPhaseMasks_decode k i j).symm

/-- Exact mask parity equals the central correction for the actual quotient generator. -/
theorem co1NonsplitFive_correction (k : Fin 5) (v : ℕ) :
    qCentralCorrection (co1BinaryAction (monsterCo1FiveGenerator k))
      (monsterCo1GeometryBinaryMaskDecode v) =
        if (co1NonsplitMaskPhase k v).testBit 0 then 1 else 0 := by
  rw [qCentralCorrection, LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toBilin'_apply, co1NonsplitFive_correction_matrix]
  exact (co1NonsplitMaskPhase_decode k v).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
