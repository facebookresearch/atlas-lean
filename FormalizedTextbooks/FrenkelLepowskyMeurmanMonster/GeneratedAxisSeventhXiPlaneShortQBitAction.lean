/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneQMatrixAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Integer masks evaluate the genuine corrected Xi action, including its central coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- XOR the actual image columns selected by the complete input mask. -/
def generatedSeventhXiShortQImageMask (x : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun j : Fin 24 =>
    if x.testBit j.val then generatedSeventhXiPlaneQColumns j else 0))

/-- The full central correction is the sum of the selected row dot products. -/
def generatedSeventhXiShortQPhaseMask (x : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if x.testBit i.val then
      monsterCo1GeometryBinaryMaskDot 24 (generatedSeventhXiPlaneQPhaseRows i) x else 0))

/-- A binary mask specifies a preferred element of the unchanged extraspecial group. -/
def generatedSeventhXiShortQMask (x : ℕ) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (n := 24) x), 1⟩

/-- The column evaluator gives every coordinate of the genuine binary image. -/
theorem generatedSeventhXiShortQImageMask_decode (x : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedSeventhXiShortQImageMask x) =
      generatedSeventhXiPlaneQMatrix *ᵥ monsterCo1GeometryBinaryMaskDecode x := by
  rw [generatedSeventhXiShortQImageMask, monsterCo1GeometryBinaryMaskDecode_sum,
    List.map_ofFn, List.sum_ofFn]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x.testBit j.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode, generatedSeventhXiPlaneQMatrix,
      golayBooleanCast, hx]

/-- The compact central evaluator is the original quadratic phase, with all linear terms. -/
theorem generatedSeventhXiShortQPhaseMask_decode (x : ℕ) :
    (if (generatedSeventhXiShortQPhaseMask x).testBit 0 then (1 : ZMod 2) else 0) =
      generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix
        (monsterCo1GeometryBinaryMaskDecode x) := by
  rw [generatedSeventhXiShortQPhaseMask, monsterCo1GeometryBinaryMaskSum_parity,
    List.map_ofFn, List.sum_ofFn]
  unfold generatedFourthLiftQMatrixPhase
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_def]
  cases hx : x.testBit i.val
  · simp [hx, monsterCo1GeometryBinaryMaskDecode]
  · simp only [ite_true]
    change (if (monsterCo1GeometryBinaryMaskDot 24
        (generatedSeventhXiPlaneQPhaseRows i) x).testBit 0 then (1 : ZMod 2) else 0) =
      ∑ j : Fin 24, monsterCo1GeometryBinaryMaskDecode x i *
        generatedSeventhXiPlaneQPhaseMatrix i j * monsterCo1GeometryBinaryMaskDecode x j
    rw [monsterCo1GeometryBinaryMaskDot_decode]
    simp only [monsterCo1GeometryBinaryMaskDecode, hx, ite_true, one_mul]
    apply Finset.sum_congr rfl
    intro j _
    cases hr : (generatedSeventhXiPlaneQPhaseRows i).testBit j.val <;>
      simp [generatedSeventhXiPlaneQPhaseMatrix, golayBooleanCast, hr]

/-- Both the actual binary image and the complete central phase have these finite mask values. -/
theorem generatedSeventhXiShortQMask_image (x : ℕ) :
    generatedSeventhXiPlaneQMatrixHom (generatedSeventhXiShortQMask x) =
      ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode
          (n := 24) (generatedSeventhXiShortQImageMask x)),
        ofAdd (if (generatedSeventhXiShortQPhaseMask x).testBit 0 then 1 else 0)⟩ := by
  apply NormalizedCocycleExtension.Extension.ext
  · change ofAdd (generatedSeventhXiPlaneQMatrix *ᵥ
        monsterCo1GeometryBinaryMaskDecode x) = _
    rw [generatedSeventhXiShortQImageMask_decode]
  · change ofAdd (0 + generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix
        (monsterCo1GeometryBinaryMaskDecode x)) = _
    rw [zero_add, generatedSeventhXiShortQPhaseMask_decode]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
