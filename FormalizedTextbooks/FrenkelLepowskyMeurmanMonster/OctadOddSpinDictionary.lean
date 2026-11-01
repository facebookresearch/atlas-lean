/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred-Q spin coordinates for the signed-octad and odd families. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortSourceClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceCodeAddition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Parker theta as the cocode part of a finite source code label. -/
def sourceWordTheta (d : Fin 4096) (k : Fin 12) : ZMod 2 :=
  if (parkerThetaMask d.val).testBit k.val then 1 else 0

/-- Half the negative-position count supplies the signed-octad Ω correction. -/
def griessOctadOmegaCoefficient (e : Fin 64) : ZMod 2 :=
  ((trialityBitWeight8 (trialityEvenMask e) / 2 : ℕ) : ZMod 2)

/-- Source weight parity and the selected bit supply the odd-vector Ω correction. -/
def griessOddOmegaCoefficient (d : Fin 2048) (j : Fin 24) : ZMod 2 :=
  (if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then 0 else 1) +
    (if (golayEncodedMask d.val).testBit j.val then 1 else 0)

/-- Exact source code translation of a signed-octad preferred Q lift. -/
theorem griessOctad_translation (d : Fin 759) (e : Fin 64) :
    spinTranslation (griessShortQ (Sum.inr (Sum.inl (d, e)))) =
      golayLabelCoefficients (golayOctadLabel d) +
        griessOctadOmegaCoefficient e • Pi.single 11 1 := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inr (Sum.inl (d, e))))
    (Fin.castAdd 12 k) = _
  rw [griessOctad_source_coordinates, leechSourceCodeWordLift_hyperbolic]
  simp only [Pi.add_apply, Fin.append_left, binaryCocodeEmbedding_left, add_zero,
    Pi.smul_apply]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
  simp [griessOctadOmegaCoefficient, -Int.natCast_ediv]

/-- Exact source cocode modulation of a signed-octad preferred Q lift. -/
theorem griessOctad_modulation (d : Fin 759) (e : Fin 64) :
    spinModulation (griessShortQ (Sum.inr (Sum.inl (d, e)))) =
      sourceWordTheta (golayOctadLabel d) +
        golaySyndrome (integerParity (griessOctadNegativeInteger d e)) := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inr (Sum.inl (d, e))))
    (Fin.natAdd 12 k) = _
  rw [griessOctad_source_coordinates, leechSourceCodeWordLift_hyperbolic]
  have hn : Fin.natAdd 12 k ≠ Fin.castAdd 12 (11 : Fin 12) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  simp only [Pi.add_apply, Fin.append_right, binaryCocodeEmbedding_right,
    Pi.smul_apply, Pi.single_apply, ite_eq_right hn, smul_zero, add_zero, sourceWordTheta]

/-- Exact source code translation of an odd-vector preferred Q lift. -/
theorem griessOdd_translation (d : Fin 2048) (j : Fin 24) :
    spinTranslation (griessShortQ (Sum.inr (Sum.inr (d, j)))) =
      golayLabelCoefficients ⟨d.val, by omega⟩ +
        griessOddOmegaCoefficient d j • Pi.single 11 1 := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inr (Sum.inr (d, j))))
    (Fin.castAdd 12 k) = _
  rw [griessOdd_source_coordinates, leechSourceCodeWordLift_hyperbolic]
  simp only [Pi.add_apply, Fin.append_left, binaryCocodeEmbedding_left, add_zero,
    Pi.smul_apply]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
  simp [griessOddOmegaCoefficient]

/-- Exact source cocode modulation of an odd-vector preferred Q lift. -/
theorem griessOdd_modulation (d : Fin 2048) (j : Fin 24) :
    spinModulation (griessShortQ (Sum.inr (Sum.inr (d, j)))) =
      sourceWordTheta ⟨d.val, by omega⟩ + (fun k => (golayGeneratorBit k j : ZMod 2)) := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inr (Sum.inr (d, j))))
    (Fin.natAdd 12 k) = _
  rw [griessOdd_source_coordinates, leechSourceCodeWordLift_hyperbolic]
  have hn : Fin.natAdd 12 k ≠ Fin.castAdd 12 (11 : Fin 12) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  simp only [Pi.add_apply, Fin.append_right, binaryCocodeEmbedding_right,
    Pi.smul_apply, Pi.single_apply, ite_eq_right hn, smul_zero, add_zero, sourceWordTheta]

/-- The actual signed-octad short lift acts on the spin coordinates by the
source character and its code/Ω translation. -/
theorem spinOperator_griessOctad (d : Fin 759) (e : Fin 64) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (d, e)))) f t =
      qSign (spinDot (sourceWordTheta (golayOctadLabel d) +
        golaySyndrome (integerParity (griessOctadNegativeInteger d e))) t) *
          f (t + (golayLabelCoefficients (golayOctadLabel d) +
            griessOctadOmegaCoefficient e • Pi.single 11 1)) := by
  change qSign (0 + spinDot (spinModulation (griessShortQ (Sum.inr (Sum.inl (d, e))))) t) *
    f (t + spinTranslation (griessShortQ (Sum.inr (Sum.inl (d, e))))) = _
  rw [griessOctad_modulation, griessOctad_translation, zero_add]

/-- The actual odd short lift acts on the spin coordinates by its source
character and its code/Ω translation. -/
theorem spinOperator_griessOdd (d : Fin 2048) (j : Fin 24) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inr (Sum.inr (d, j)))) f t =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩ +
        (fun k => (golayGeneratorBit k j : ZMod 2))) t) *
          f (t + (golayLabelCoefficients ⟨d.val, by omega⟩ +
            griessOddOmegaCoefficient d j • Pi.single 11 1)) := by
  change qSign (0 + spinDot (spinModulation (griessShortQ (Sum.inr (Sum.inr (d, j))))) t) *
    f (t + spinTranslation (griessShortQ (Sum.inr (Sum.inr (d, j))))) = _
  rw [griessOdd_modulation, griessOdd_translation, zero_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
