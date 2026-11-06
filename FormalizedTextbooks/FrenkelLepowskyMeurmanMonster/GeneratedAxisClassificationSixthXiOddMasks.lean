/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOddThetaCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSyndromeMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates

/-! Exact preferred odd-Q masks retain the actual Parker theta and coordinate character. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Complete preferred odd-Q mask with its original omega correction and coordinate character. -/
def generatedSixthXiOddMask (f : Fin 512) (j : Fin 24) : ℕ :=
  generatedSixthXiJoinMasks
    (nortonUIntegerLabel
      (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩ +
        griessOddOmegaCoefficient (generatedSixthMonomialOddCode f) j • Pi.single 11 1))
    (Nat.xor (generatedSixthXiOddThetaLabels f).val (generatedSixthXiSyndromeColumns j))

/-- The complete mask is the genuine preferred odd lift, with central coefficient zero. -/
theorem generatedSixth_xi_odd_mask_Q (f : Fin 512) (j : Fin 24) :
    griessShortQ (Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j))) =
      generatedSixthXiMaskQ (generatedSixthXiOddMask f j) := by
  rw [← monsterNortonShortQSource_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append
      (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩ +
        griessOddOmegaCoefficient (generatedSixthMonomialOddCode f) j • Pi.single 11 1)
      (sourceWordTheta ⟨(generatedSixthMonomialOddCode f).val, by omega⟩ +
        (fun k => (golayGeneratorBit k j : ZMod 2))) =
      monsterCo1GeometryBinaryMaskDecode (generatedSixthXiOddMask f j)
    rw [generatedSixthXiOddMask, generatedSixth_xi_join_masks_decode,
      nortonUIntegerLabel_inverse, monsterCo1GeometryBinaryMaskDecode_xor,
      generatedSixth_xi_odd_theta_cache]
    congr 1
    funext k
    simp only [Pi.add_apply, golayLabelCoefficients, monsterCo1GeometryBinaryMaskDecode]
    congr 1
    exact (generatedSixth_xi_syndrome_columns j k).symm
  · rfl

/-- Every actual binary coordinate of the preferred odd lift is its exact displayed mask bit. -/
theorem generatedSixth_xi_odd_mask_base (f : Fin 512) (j : Fin 24) :
    toAdd (griessShortQ
      (Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j)))).base =
        monsterCo1GeometryBinaryMaskDecode (generatedSixthXiOddMask f j) := by
  rw [generatedSixth_xi_odd_mask_Q]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
