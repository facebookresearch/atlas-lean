/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalShort

/-! Catalogue-free exact signed-octad coefficients of the genuine canonical middle packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem octad_label_injective : Function.Injective golayOctadLabel := by
  intro o p h
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  apply Subtype.ext
  exact h

/-- Genuine source octad labels are selected exactly by their full code and sign descriptors. -/
theorem generatedSeventhXiShortOutputLabel_octad_iff (s : Fin 2) (p : Fin 276)
    (o : Fin 759) (e : Fin 64) :
    Sum.inr (Sum.inl (o, e)) = generatedSeventhXiShortOutputLabel s p ↔
      generatedSeventhXiShortDescriptor s p 0 = 1 ∧
      generatedSeventhXiShortDescriptor s p 1 = (golayOctadLabel o).val ∧
      generatedSeventhXiShortDescriptor s p 2 = e.val := by
  by_cases h0 : generatedSeventhXiShortDescriptor s p 0 = 0
  · simp [generatedSeventhXiShortOutputLabel, h0]
  · by_cases h1 : generatedSeventhXiShortDescriptor s p 0 = 1
    · have hc : (golayOctadLabel (generatedSeventhXiShortOutputOctad s p h1)).val =
          generatedSeventhXiShortDescriptor s p 1 :=
        congrArg Fin.val (generatedSeventhXiShortOutputOctad_code s p h1)
      have he : o = generatedSeventhXiShortOutputOctad s p h1 ↔
          generatedSeventhXiShortDescriptor s p 1 = (golayOctadLabel o).val := by
        constructor
        · intro ho
          subst o
          exact hc.symm
        · intro ho
          apply octad_label_injective
          apply Fin.ext
          exact ho.symm.trans hc.symm
      have hb : generatedSeventhXiShortDescriptor s p 2 < 64 :=
        (generatedSeventhXiShort_octad_data s p h1).2.2.1
      simp only [generatedSeventhXiShortOutputLabel, h1, Nat.one_ne_zero, dite_false, dite_true,
        Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, he, Fin.ext_iff,
        Nat.mod_eq_of_lt hb, true_and]
      tauto
    · simp [generatedSeventhXiShortOutputLabel, h0, h1]

/-- The complete source sum selects every original signed-octad coefficient and central phase. -/
def generatedSeventhXiMiddleOctadNumerator (c : Fin 4096) (e : Fin 64) : ℤ :=
  ∑ s : Fin 2, ∑ p : Fin 276,
    generatedSeventhXiShortInputWeight s p *
      nortonUIntegerSign (generatedSeventhXiShortPhaseBit s p : ZMod 2) *
      (if generatedSeventhXiShortDescriptor s p 0 = 1 ∧
          generatedSeventhXiShortDescriptor s p 1 = c.val ∧
          generatedSeventhXiShortDescriptor s p 2 = e.val then 1 else 0)

/-- The finite code-and-sign sum equals the entire genuine preferred-label numerator. -/
theorem generatedSeventhXiMiddleOctadNumerator_eq (o : Fin 759) (e : Fin 64) :
    generatedSeventhXiMiddleOctadNumerator (golayOctadLabel o) e =
      generatedSeventhXiMiddleShortNumerator (Sum.inr (Sum.inl (o, e))) := by
  unfold generatedSeventhXiMiddleOctadNumerator generatedSeventhXiMiddleShortNumerator
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : Sum.inr (Sum.inl (o, e)) = generatedSeventhXiShortOutputLabel s p
  · have hd := (generatedSeventhXiShortOutputLabel_octad_iff s p o e).mp he
    simp only [ite_eq_left he, ite_eq_left hd]
  · have hd := mt (generatedSeventhXiShortOutputLabel_octad_iff s p o e).mpr he
    simp only [ite_eq_right he, ite_eq_right hd]

/-- Actual incoming octad coordinates retain their complete signed numerator divided by four. -/
theorem generatedSeventhXi_middle_octad_arithmetic (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.1
      (Sum.inr (Sum.inl (o, e))) =
        (generatedSeventhXiMiddleOctadNumerator (golayOctadLabel o) e : ℝ) / 4 := by
  rw [generatedSeventhXi_canonical_middle_short, generatedSeventhXiMiddleOctadNumerator_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
