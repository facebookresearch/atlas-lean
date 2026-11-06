/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadQFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSyndromeMasks

/-! Complete preferred octad-Q masks retain the actual theta and negative-position syndrome. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred octad-Q mask, including its genuine omega translation correction. -/
def generatedSixthXiOctadMask (f : Fin 231) (e : Fin 64) : ℕ :=
  generatedSixthXiJoinMasks
    (nortonUIntegerLabel (golayLabelCoefficients (generatedSixthFinalOctadCacheCode f) +
      griessOctadOmegaCoefficient e • Pi.single 11 1))
    (Nat.xor (generatedSixthXiOctadThetaLabels f).val
      (generatedSixthXiSyndromeMask (generatedSixthMonomialOctadNegativeMask f e)))

/-- The complete mask is the genuine preferred octad lift, including its central coefficient. -/
theorem generatedSixth_xi_octad_mask_Q (f : Fin 231) (e : Fin 64) :
    griessShortQ (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) =
      generatedSixthXiMaskQ (generatedSixthXiOctadMask f e) := by
  rw [generatedSixth_xi_octad_Q_fast]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append
      (golayLabelCoefficients (generatedSixthFinalOctadCacheCode f) +
        griessOctadOmegaCoefficient e • Pi.single 11 1)
      (golayLabelCoefficients (generatedSixthXiOctadThetaLabels f) +
        golaySyndrome (integerParity (generatedSixthMonomialOctadNegativeInteger f e))) =
      monsterCo1GeometryBinaryMaskDecode (generatedSixthXiOctadMask f e)
    rw [generatedSixthXiOctadMask, generatedSixth_xi_join_masks_decode,
      nortonUIntegerLabel_inverse, monsterCo1GeometryBinaryMaskDecode_xor,
      generatedSixth_xi_syndrome_mask]
    have hp := generatedSixth_xi_integer_mask_parity
      (generatedSixthMonomialOctadNegativeMask f e)
    change integerParity (generatedSixthMonomialOctadNegativeInteger f e) = _ at hp
    rw [← hp]
    rfl
  · rfl

/-- Every original binary coordinate of the preferred octad lift is its exact mask bit. -/
theorem generatedSixth_xi_octad_mask_base (f : Fin 231) (e : Fin 64) :
    toAdd (griessShortQ
      (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e)))).base =
        monsterCo1GeometryBinaryMaskDecode (generatedSixthXiOctadMask f e) := by
  rw [generatedSixth_xi_octad_mask_Q]
  rfl

/-- The scalar mask evaluator is the true full corrected Xi phase on every original octad. -/
theorem generatedSixth_xi_octad_mask_phase (f : Fin 231) (e : Fin 64) :
    localShortPhase (generatedSixthCorrectedGenerator 4)
      (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) =
        generatedSixthXiSelectedPhase (generatedSixthXiMaskQ (generatedSixthXiOctadMask f e)) := by
  rw [generatedSixth_xi_short_selected_phase, generatedSixth_xi_octad_mask_Q]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
