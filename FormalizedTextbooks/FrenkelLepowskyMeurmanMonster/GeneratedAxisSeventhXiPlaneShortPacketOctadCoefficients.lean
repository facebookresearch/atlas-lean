/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedSourceBasics
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadFourierArithmetic

/-! Original positive-triality octad coefficients and their complete packed family numerators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The finite Fourier numerator is the whole original sixty-four-row operation. -/
theorem generatedSeventhXiShortPackedOctadCoefficient_actual (g : Fin 231) (e : Fin 64) :
    generatedSeventhXiShortPackedOctadCoefficient g e =
      generatedSeventhXiOctadFourierNumerator g e := by
  simp only [generatedSeventhXiShortPackedOctadCoefficient,
    generatedSeventhXiShortPackedOctadSlot_actual, generatedSeventhXiShortPackedFourierSign_actual,
    generatedSeventhXiOctadFourierNumerator]

private theorem octad_label_injective : Function.Injective golayOctadLabel := by
  intro o p h
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  exact Subtype.ext h

private theorem family_eq_iff (g : Fin 231) (o : Fin 759) :
    generatedSeventhXiOctadCodes g = (golayOctadLabel o).val ↔
      generatedSeventhXiOctadFamily g = o := by
  constructor
  · intro h
    apply octad_label_injective
    rw [generatedSeventhXiOctadFamily_code]
    exact Fin.ext h
  · intro h
    have hc := generatedSeventhXiOctadFamily_code g
    rw [h] at hc
    exact (congrArg Fin.val hc).symm

/-- Every original outgoing octad coordinate is the complete signed family sum. -/
theorem generatedSeventhXiShortOctadCoefficient_sum (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (Sum.inr (Sum.inl (o, e))) =
        ∑ g : Fin 231,
          if generatedSeventhXiOctadFamily g = o then
            (generatedSeventhXiShortPackedOctadCoefficient g e : ℝ) / 32 else 0 := by
  rw [generatedSeventhXi_canonical_octad_fourier]
  simp_rw [← generatedSeventhXiShortPackedOctadCoefficient_actual, family_eq_iff]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
