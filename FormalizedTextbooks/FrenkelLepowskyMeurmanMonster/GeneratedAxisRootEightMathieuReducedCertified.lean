/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuCompactSources
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuCompactSourceEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveMatrixBinding

/-! Unconditional genuine reduced compact lifts; full short and tensor fixation remain obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Literal full-Q translation data found by exact numerical discovery on the positive tensor. -/
def generatedRootEightMathieuReducedTranslation : Fin 2 → Nat := ![115, 15]

/-- Literal modulation data in the original twelve-coordinate Schrödinger basis. -/
def generatedRootEightMathieuReducedModulation : Fin 2 → Nat := ![105, 1349]

/-- The literal central coefficients of the two discovered corrections. -/
def generatedRootEightMathieuReducedConstant : Fin 2 → ZMod 2 := ![1, 0]

/-- Genuine original Q elements; these data alone do not assert whole-axis fixation. -/
def generatedRootEightMathieuReducedCorrection (j : Fin 2) : Q :=
  ⟨ofAdd (fun i => if i.val < 12 then
      if (generatedRootEightMathieuReducedTranslation j).testBit i.val then 1 else 0
    else if (generatedRootEightMathieuReducedModulation j).testBit (i.val - 12) then 1 else 0),
    ofAdd (generatedRootEightMathieuReducedConstant j)⟩

/-- The entire actual reduced corrected fibers with all full-Q comparisons proved. -/
def generatedRootEightMathieuReducedCertifiedFiber (j : Fin 2) : localFiberSubgroup :=
  generatedRootEightMathieuReducedCorrectedFiber
    generatedRootEight_m22_compact_source_condition_00
    generatedRootEight_m22_compact_source_condition_01
    generatedRootEight_m22_compact_source_condition_04
    generatedRootEight_m22_compact_source_condition_08
    (generatedRootEightMathieuReducedCorrection j) j

/-- Each corrected reduced generator is an actual full local group element. -/
def generatedRootEightMathieuReducedCertifiedLocal (j : Fin 2) : H :=
  localFiberIntoH (generatedRootEightMathieuReducedCertifiedFiber j)

/-- The complete original positive spatial maps are retained unconditionally. -/
theorem generatedRootEight_mathieu_reduced_certified_spatial (j : Fin 2) :
    (generatedRootEightMathieuReducedCertifiedFiber j).val.2 =
      golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j) :=
  generatedRootEight_mathieu_reduced_corrected_spatial _ _ _ _ _ _

/-- The actual reduced generators have their genuine original Conway projections. -/
theorem generatedRootEight_mathieu_reduced_certified_projection (j : Fin 2) :
    projH (generatedRootEightMathieuReducedCertifiedLocal j) =
      QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j)) :=
  generatedRootEight_mathieu_reduced_local_projection _ _ _ _ _ _

/-- The corrected actual reduced pair generates the entire genuine Mathieu projected point image. -/
theorem generatedRootEight_mathieu_reduced_certified_generated :
    Subgroup.closure (Set.range fun j => projH (generatedRootEightMathieuReducedCertifiedLocal j)) =
      (leechNormSixHS100PairPointStabilizer.map
        (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion).subtype).map
          (QuotientGroup.mk' signsSubgroup) :=
  generatedRootEight_mathieu_reduced_projected_generated _ _ _ _ _

/-- The complete actual canonical positive matrix is fixed without any tensor premise. -/
theorem generatedRootEight_mathieu_reduced_certified_matrix (j : Fin 2) :
    localMatrixRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 := by
  rw [generatedRootEight_canonical_positive_matrix_actual]
  exact generatedRootEight_mathieu_reduced_corrected_matrix _ _ _ _ _ _

/-- Every signed-short coordinate of an actual corrected reduced lift remains to be fixed. -/
def generatedRootEightMathieuReducedShortCondition (j : Fin 2) : Prop :=
  ∀ r, localShortRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r

/-- Every tensor coordinate, including zero entries and its genuine phase, remains to be fixed. -/
def generatedRootEightMathieuReducedTensorCondition (j : Fin 2) : Prop :=
  ∀ t i, localTensorRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i

/-- The full-coordinate short and tensor obligations suffice for actual whole-axis fixation. -/
theorem generatedRootEight_mathieu_reduced_certified_axis_of_coordinates (j : Fin 2)
    (hC : generatedRootEightMathieuReducedShortCondition j)
    (hT : generatedRootEightMathieuReducedTensorCondition j) :
    rhoLocal (generatedRootEightMathieuReducedCertifiedLocal j)
      generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis := by
  change localGriessRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
    generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis
  have hm := generatedRootEight_mathieu_reduced_certified_matrix j
  have hs : localShortRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 := funext hC
  have ht : localTensorRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 :=
    funext fun t => funext (hT t)
  have he : griessConwayEncode
      (localGriessRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
        generatedRootEightCanonicalPositiveAxis) =
      griessConwayEncode generatedRootEightCanonicalPositiveAxis := by
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change (localMatrixRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1,
        (localShortRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
          (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1,
          localTensorRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
            (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2)) = _
    rw [hm, hs, ht]
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
