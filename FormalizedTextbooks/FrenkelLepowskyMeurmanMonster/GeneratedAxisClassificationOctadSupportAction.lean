/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhysicalSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ProjectionStabilizer

/-! Actual section-preserving Leech elements permute exactly the supported short labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual short permutation of a section-preserving element preserves its short support. -/
theorem generatedOctadShortSupport_permutation (o : Fin 759) (g : leechIsomSubgroup)
    (hg : generatedOctadPreserves (golayOctadWord o) g) (r : GriessShortIndex)
    (hr : generatedOctadShortSupport o r) :
    generatedOctadShortSupport o (griessShortPermutation g r) := by
  apply (generatedOctadShortSupport_iff_physical o _).mpr
  intro i hi
  have hci : golayOctadWord o i = 0 := by
    simp only [golayOctadWord, golayLabelEncoder_boolean, hi, golayBooleanCast]
    rfl
  have hz : g.val (griessShortVector r) i = 0 := by
    rw [← leechIsomMatrix_mulVec]
    change (∑ j, leechIsomMatrix g i j * griessShortVector r j) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : golayOctadWord o j = 0
    · have hb : (golayEncodedMask (golayOctadLabel o).val).testBit j.val = false := by
        have hnot : j ∉ golayOctadSupport o := by
          rw [← golayOctadWord_ne_zero_iff]
          exact not_not.mpr hj
        simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
          Finset.mem_univ, true_and, Bool.not_eq_true] using hnot
      rw [generatedAxisE8_short_support_zero o r hr j hb, mul_zero]
    · rw [generatedAxisE8_preserving_matrix_zero _ g hg i j hci hj, zero_mul]
  rcases griessShortPermutation_vector g r with he | he
  · rw [he] at hz
    exact hz
  · rw [he] at hz
    simpa only [Pi.neg_apply, neg_eq_zero] using hz

/-- The actual short support is preserved in both directions, including the inverse action. -/
theorem generatedOctadShortSupport_permutation_iff (o : Fin 759) (g : leechIsomSubgroup)
    (hg : generatedOctadPreserves (golayOctadWord o) g) (r : GriessShortIndex) :
    generatedOctadShortSupport o (griessShortPermutation g r) ↔
      generatedOctadShortSupport o r := by
  constructor
  · intro h
    have hh := generatedOctadShortSupport_permutation o g⁻¹
      (generatedAxisE8_preserves_inv _ g hg) (griessShortPermutation g r) h
    rw [map_inv] at hh
    change generatedOctadShortSupport o
      ((griessShortPermutation g).symm (griessShortPermutation g r)) at hh
    rwa [Equiv.symm_apply_apply] at hh
  · exact generatedOctadShortSupport_permutation o g hg r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
