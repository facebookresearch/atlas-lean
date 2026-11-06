/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthOctadNegativeCharacter

/-! The genuine preferred octad syndrome is an eight-coordinate XOR with no lattice inversion. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Only the eight genuine negative octad coordinates contribute to the original syndrome. -/
def generatedSixthXiOctadEightSyndrome (f : Fin 231) (e : Fin 64) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun a : Fin 8 =>
    if (trialityEvenMask e).testBit a.val then
      generatedSixthXiSyndromeColumns (generatedSixthMonomialOctadCoordinates f a) else 0))

/-- The eight-coordinate XOR is exactly the original genuine preferred negative syndrome. -/
theorem generatedSixth_xi_octad_eight_syndrome (f : Fin 231) (e : Fin 64) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedSixthXiOctadEightSyndrome f e) =
      golaySyndrome (integerParity
        (griessOctadNegativeInteger (generatedSixthFinalOctadCacheOctad f) e)) := by
  rw [generatedSixthXiOctadEightSyndrome, monsterCo1GeometryBinaryMaskDecode_sum,
    List.map_ofFn, List.sum_ofFn]
  funext k
  simp only [Finset.sum_apply]
  change (∑ a : Fin 8, monsterCo1GeometryBinaryMaskDecode
    (if (trialityEvenMask e).testBit a.val then
      generatedSixthXiSyndromeColumns (generatedSixthMonomialOctadCoordinates f a) else 0) k) =
    ∑ i : Fin 24, integerParity
      (griessOctadNegativeInteger (generatedSixthFinalOctadCacheOctad f) e) i *
        (golayGeneratorBit k i : ZMod 2)
  simp_rw [generatedSixth_octad_negative_indicator, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    generatedSixth_monomial_octad_coordinates]
  cases (trialityEvenMask e).testBit a.val
  · simp [monsterCo1GeometryBinaryMaskDecode]
  · simp only [ite_true, one_mul]
    exact generatedSixth_xi_syndrome_columns _ k

/-- Complete original octad-Q mask using only its eight actual syndrome contributors. -/
def generatedSixthXiOctadMaskEight (f : Fin 231) (e : Fin 64) : ℕ :=
  generatedSixthXiJoinMasks
    (nortonUIntegerLabel (golayLabelCoefficients (generatedSixthFinalOctadCacheCode f) +
      griessOctadOmegaCoefficient e • Pi.single 11 1))
    (Nat.xor (generatedSixthXiOctadThetaLabels f).val (generatedSixthXiOctadEightSyndrome f e))

/-- The accelerated mask retains every coordinate and the center of the actual preferred Q lift. -/
theorem generatedSixth_xi_octad_mask_eight_Q (f : Fin 231) (e : Fin 64) :
    griessShortQ (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) =
      generatedSixthXiMaskQ (generatedSixthXiOctadMaskEight f e) := by
  rw [← monsterNortonShortQSource_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append
      (golayLabelCoefficients (golayOctadLabel (generatedSixthFinalOctadCacheOctad f)) +
        griessOctadOmegaCoefficient e • Pi.single 11 1)
      (sourceWordTheta (golayOctadLabel (generatedSixthFinalOctadCacheOctad f)) +
        golaySyndrome (integerParity
          (griessOctadNegativeInteger (generatedSixthFinalOctadCacheOctad f) e))) =
      monsterCo1GeometryBinaryMaskDecode (generatedSixthXiOctadMaskEight f e)
    rw [generatedSixthXiOctadMaskEight, generatedSixth_xi_join_masks_decode,
      nortonUIntegerLabel_inverse, monsterCo1GeometryBinaryMaskDecode_xor,
      generatedSixth_xi_octad_eight_syndrome, generatedSixth_final_octad_cache_label,
      generatedSixth_xi_octad_theta_cache]
    rfl
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
