/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire actual seventh short state as a finite sum of the reached octad units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OctadSeventhCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem output_ne_other_octad (a : Fin 64) (k : Fin 16) (d : Fin 759) (e : Fin 64)
    (hd : ∀ j, monsterNortonLine01OctadIndex j ≠ d) :
    monsterNortonLine01ShortInverseOutput a k ≠ Sum.inr (Sum.inl (d, e)) := by
  unfold monsterNortonLine01ShortInverseOutput
  split_ifs
  · change Sum.inr (Sum.inl
      (monsterNortonLine01OctadIndex (monsterNortonLine01ShortInverseOctadId a k),
        monsterNortonLine01ShortInverseOctadSigns a k)) ≠ Sum.inr (Sum.inl (d, e))
    intro h
    exact hd _ (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))).1
  · simp only [ne_eq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true]

private theorem sixth_other_octad_zero (d : Fin 759) (e : Fin 64)
    (hd : ∀ j, monsterNortonLine01OctadIndex j ≠ d) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.1
      (Sum.inr (Sum.inl (d, e))) = 0 := by
  change monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV
    (Sum.inr (Sum.inl (d, e))) = 0
  rw [monsterNortonLine01ShortSixthInteger_actual]
  have hn : monsterNortonLine01ShortSixthIntegerNumerator (Sum.inr (Sum.inl (d, e))) = 0 := by
    simp only [monsterNortonLine01ShortSixthIntegerNumerator, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Ne.symm (output_ne_other_octad _ _ d e hd), ite_false, mul_zero, Finset.sum_const_zero]
  simp only [Pi.smul_apply, smul_eq_mul, hn, Int.cast_zero, mul_zero]

/-- No other actual octad block occurs in the seventh short state. -/
theorem monsterNortonLine01ShortSeventh_other_octad_zero (d : Fin 759) (e : Fin 64)
    (hd : ∀ j, monsterNortonLine01OctadIndex j ≠ d) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1
      (Sum.inr (Sum.inl (d, e))) = 0 := by
  rw [monsterNortonLine01ShortSeventh_octad_coordinates]
  have h : (fun r => monsterNortonShortProjection
      monsterNortonLine01TensorAfterVUExtraInverseVInverseUV (Sum.inr (Sum.inl (d, r)))) = 0 := by
    funext r
    exact sixth_other_octad_zero d r hd
  rw [h, map_zero]
  rfl

/-- The complete seventh short expansion in the actual sixteen reached octad blocks. -/
noncomputable def monsterNortonLine01ShortSeventhExpansion : GriessShortIndex → ℝ :=
  (1 / 512 : ℝ) • ∑ j : Fin 16, ∑ e : Fin 64,
    (monsterNortonLine01OctadSeventhCoefficientLookup j e : ℝ) •
      Pi.single (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) 1

/-- The entire actual seventh short coordinate equals its finite signed octad-unit expansion. -/
theorem monsterNortonLine01ShortSeventhExpansion_actual :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1 =
      monsterNortonLine01ShortSeventhExpansion := by
  funext r
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
  · rw [monsterNortonLine01PairSeventh_zero]
    simp only [monsterNortonLine01ShortSeventhExpansion, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul, Pi.single_apply, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero]
  · by_cases h : ∃ j, monsterNortonLine01OctadIndex j = d
    · obtain ⟨j, rfl⟩ := h
      rw [monsterNortonLine01OctadSeventh_coordinates]
      simp only [monsterNortonLine01ShortSeventhExpansion, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, Pi.single_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
        monsterNortonLine01OctadIndex_injective.eq_iff, mul_ite, mul_one, mul_zero,
        ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.sum_const_zero]
    · have hd : ∀ j, monsterNortonLine01OctadIndex j ≠ d := by
        simpa only [not_exists] using h
      rw [monsterNortonLine01ShortSeventh_other_octad_zero d e hd]
      simp only [monsterNortonLine01ShortSeventhExpansion, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, Pi.single_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
      have hc (j : Fin 16) (a : Fin 64) : ¬ (d = monsterNortonLine01OctadIndex j ∧ e = a) := by
        rintro ⟨hj, _⟩
        exact hd j hj.symm
      simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]
  · rw [monsterNortonLine01TensorSeventh_odd_short_zero]
    simp only [monsterNortonLine01ShortSeventhExpansion, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false, mul_zero,
      Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
