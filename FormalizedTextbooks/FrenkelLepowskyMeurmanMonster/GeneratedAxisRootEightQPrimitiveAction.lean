/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitiveRows
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalLift
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQMaskGeneric
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitive10

/-! Actual full extraspecial root-eight primitive actions from certified basis data. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual original local fibers of the eleven source factors. -/
def generatedRootEightQPrimitiveFiber (k : Fin 11) : localFiberSubgroup :=
  if h : k.val < 4 then generatedFifthRootEightCanonicalFiberLetter ⟨k.val, h⟩
  else if k.val = 4 then xiSpinLocalFiber
  else generatedFifthSignFiber
    (generatedRootEightQPrimitiveSignLabels ⟨k.val - 5, by omega⟩) 0

/-- The finite primitive evaluator is the entire actual fiber conjugation on Q. -/
theorem generatedRootEight_Q_primitive_image (k : Fin 11) (q : Q) :
    spinConjugation (generatedRootEightQPrimitiveFiber k).val.1 q =
      generatedRootEightQPrimitiveImage k q := by
  fin_cases k
  · exact monsterSourcePermutationSpin_conjugation 0 q
  · exact monsterSourcePermutationSpin_conjugation 1 q
  · exact generatedAxisGlobalMonomialInverse_QImage 0 q
  · exact generatedAxisGlobalMonomialInverse_QImage 1 q
  · exact xiSpinHolomorph_conjugation q
  · exact generatedAxisGlobalSignFull_QImage 1 q
  · exact generatedAxisGlobalSignFull_QImage 2048 q
  · exact generatedAxisGlobalSignFull_QImage 2816 q
  · exact generatedAxisGlobalSignFull_QImage 1536 q
  · exact generatedAxisGlobalSignFull_QImage 3220 q
  · exact generatedAxisGlobalSignFull_QImage 165 q

/-- All original primitive images have their certified complete basis coordinates. -/
theorem generatedRootEight_Q_primitive_basis_actual (k : Fin 11) (i : Fin 24) :
    spinConjugation (generatedRootEightQPrimitiveFiber k).val.1 (qCoordinateGenerator i) =
      generatedRootEightQPrimitiveBasisImage k i := by
  rw [generatedRootEight_Q_primitive_image]
  fin_cases k
  · exact generatedRootEight_Q_primitive_00_actual i
  · exact generatedRootEight_Q_primitive_01_actual i
  · exact generatedRootEight_Q_primitive_02_actual i
  · exact generatedRootEight_Q_primitive_03_actual i
  · exact generatedRootEight_Q_primitive_04_actual i
  · exact generatedRootEight_Q_primitive_05_actual i
  · exact generatedRootEight_Q_primitive_06_actual i
  · exact generatedRootEight_Q_primitive_07_actual i
  · exact generatedRootEight_Q_primitive_08_actual i
  · exact generatedRootEight_Q_primitive_09_actual i
  · exact generatedRootEight_Q_primitive_10_actual i

/-- Every original primitive preserves the actual binary square form. -/
theorem generatedRootEight_Q_primitive_square (k : Fin 11) (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation (generatedRootEightQPrimitiveFiber k).val.1) v) = squareQuad v := by
  change squareQuad (spinBinaryAction (generatedRootEightQPrimitiveFiber k).val.1 v) = _
  rw [(generatedRootEightQPrimitiveFiber k).property]
  exact leechBinaryAction_squareQuad _ v

/-- Certified columns and cocycle rows give every full original primitive Q-mask image. -/
theorem generatedRootEight_Q_primitive_mask_actual (k : Fin 11) (v : ℕ) :
    spinConjugation (generatedRootEightQPrimitiveFiber k).val.1 (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedRootEightQPrimitiveColumns k)
        (generatedRootEightQPrimitiveRows k) (generatedRootEightQPrimitiveCoefficients k) v := by
  apply generatedNinth_lower_spin_q_mask_from_units _
    (generatedRootEight_Q_primitive_square k) (generatedRootEightQPrimitiveBasisImage k)
    _ _ _ (generatedRootEight_Q_primitive_basis_actual k)
  · intro i
    rfl
  · exact generatedRootEight_Q_primitive_rows_actual k
  · intro i
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
