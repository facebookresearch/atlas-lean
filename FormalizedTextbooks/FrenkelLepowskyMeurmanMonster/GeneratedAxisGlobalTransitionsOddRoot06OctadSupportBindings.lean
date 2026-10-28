/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFrame
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSupportCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSparseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhysicalSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupportCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadQBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Every source support vector reaches its actual original standard-octad label; the complete target support is covered. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

/-- Every complete preferred-vector image under the genuine original frame has its certified physical sign. -/
theorem generatedAxisGlobalOddRoot06OctadShortVector_frame (p : Fin 120) :
    generatedAxisGlobalOddRoot06OctadStandardFrameIsometry.val
      (griessShortVector (generatedAxisGlobalOddRoot06OctadSourceLabel p)) =
    (generatedAxisGlobalOddRoot06OctadVectorSign p : ℝ) •
      griessShortVector (generatedAxisGlobalOddRoot06OctadTargetLabel p) := by
  ext i
  rw [← leechIsomMatrix_mulVec, generatedAxisGlobalOddRoot06OctadStandardFrame_actual]
  have hs := generatedAxisGlobalOddRoot06OctadShortFrame_certificate p i
  have hsum : generatedAxisGlobalOddRoot06OctadFrameShortQ p i =
      ∑ j : Fin 24, generatedAxisGlobalOddRoot06OctadStandardFrameQ i j *
        (generatedAxisGlobalShortIntegral (generatedAxisGlobalOddRoot06OctadSourceLabel p) j : ℚ) := by
    unfold generatedAxisGlobalOddRoot06OctadFrameShortQ
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · simp only [hj, zero_mul]
    · rfl
  rw [hsum] at hs
  have hr : (∑ j : Fin 24, (generatedAxisGlobalOddRoot06OctadStandardFrameQ i j : ℝ) *
      (generatedAxisGlobalShortIntegral (generatedAxisGlobalOddRoot06OctadSourceLabel p) j : ℝ)) =
      (generatedAxisGlobalOddRoot06OctadVectorSign p : ℝ) *
        (generatedAxisGlobalShortIntegral (generatedAxisGlobalOddRoot06OctadTargetLabel p) i : ℝ) := by
    exact_mod_cast hs
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, griessShortVector,
    ← generatedAxisGlobalShortIntegral_actual, Pi.smul_apply, smul_eq_mul]
  change (∑ j : Fin 24, (generatedAxisGlobalOddRoot06OctadStandardFrameQ i j : ℝ) *
    ((generatedAxisGlobalShortIntegral (generatedAxisGlobalOddRoot06OctadSourceLabel p) j : ℝ) /
      Real.sqrt 8)) = _
  simp only [← mul_div_assoc, ← Finset.sum_div]
  rw [hr]

/-- Source preferred-short labels are distinct because all 120 labels round trip through their actual keys. -/
theorem generatedAxisGlobalOddRoot06OctadSourceLabel_injective :
    Function.Injective generatedAxisGlobalOddRoot06OctadSourceLabel := by
  intro p q hpq
  have hp := generatedAxisGlobalOddRoot06OctadSparse_roundtrip p
  rw [hpq, generatedAxisGlobalOddRoot06OctadSparse_roundtrip q] at hp
  exact Option.some.inj hp.symm

/-- Exact physical transport identifies the genuine preferred-short permutation of every source support label. -/
theorem generatedAxisGlobalOddRoot06OctadShortPermutation_frame (p : Fin 120) :
    griessShortPermutation generatedAxisGlobalOddRoot06OctadStandardFrameIsometry
      (generatedAxisGlobalOddRoot06OctadSourceLabel p) =
        generatedAxisGlobalOddRoot06OctadTargetLabel p := by
  apply centralizer_shortVector_sign_unique
  have hc := generatedAxisGlobalOddRoot06OctadShortVector_frame p
  have hh : generatedAxisGlobalOddRoot06OctadStandardFrameIsometry.val
      (griessShortVector (generatedAxisGlobalOddRoot06OctadSourceLabel p)) =
      griessShortVector (generatedAxisGlobalOddRoot06OctadTargetLabel p) ∨
    generatedAxisGlobalOddRoot06OctadStandardFrameIsometry.val
      (griessShortVector (generatedAxisGlobalOddRoot06OctadSourceLabel p)) =
      -griessShortVector (generatedAxisGlobalOddRoot06OctadTargetLabel p) := by
    rcases generatedAxisGlobalOddRoot06OctadVectorSign_unit p with hs | hs
    · left
      simpa only [hs, Int.cast_one, one_smul] using hc
    · right
      simpa only [hs, Int.cast_neg, Int.cast_one, neg_one_smul] using hc
  rcases griessShortPermutation_vector generatedAxisGlobalOddRoot06OctadStandardFrameIsometry
    (generatedAxisGlobalOddRoot06OctadSourceLabel p) with hp | hn
  · rcases hh with hh | hh
    · exact Or.inl (hp.symm.trans hh)
    · exact Or.inr (hp.symm.trans hh)
  · rcases hh with hh | hh
    · right
      have he := congrArg Neg.neg (hn.symm.trans hh)
      simpa only [neg_neg] using he
    · left
      have he := congrArg Neg.neg (hn.symm.trans hh)
      simpa only [neg_neg] using he

/-- Every target label is an actual preferred short line in the original standard octad. -/
theorem generatedAxisGlobalOddRoot06OctadTarget_supported (p : Fin 120) :
    generatedOctadShortSupport generatedOctadBasisOctad
      (generatedAxisGlobalOddRoot06OctadTargetLabel p) := by
  apply (generatedOctadShortSupport_iff_physical _ _).mpr
  intro i hi
  rw [generatedOctadBasisOctad_mask] at hi
  have hz := generatedAxisGlobalOddRoot06OctadTarget_physical_support p i hi
  simp only [griessShortVector, ← generatedAxisGlobalShortIntegral_actual, hz, Int.cast_zero, zero_div]

/-- The complete target preferred-short support contains no repeated actual labels. -/
theorem generatedAxisGlobalOddRoot06OctadTargetLabel_injective :
    Function.Injective generatedAxisGlobalOddRoot06OctadTargetLabel := by
  intro p q hpq
  apply generatedAxisGlobalOddRoot06OctadSourceLabel_injective
  apply (griessShortPermutation generatedAxisGlobalOddRoot06OctadStandardFrameIsometry).injective
  rw [generatedAxisGlobalOddRoot06OctadShortPermutation_frame,
    generatedAxisGlobalOddRoot06OctadShortPermutation_frame, hpq]

/-- Every actual standard-octad short line is covered by the complete original transformed support. -/
theorem generatedAxisGlobalOddRoot06OctadTarget_coverage (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    ∃ p : Fin 120, generatedAxisGlobalOddRoot06OctadTargetLabel p = r := by
  let f : Fin 120 → {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} :=
    fun p => ⟨generatedAxisGlobalOddRoot06OctadTargetLabel p,
      generatedAxisGlobalOddRoot06OctadTarget_supported p⟩
  have hi : Function.Injective f := by
    intro p q hpq
    exact generatedAxisGlobalOddRoot06OctadTargetLabel_injective (congrArg Subtype.val hpq)
  have hc : Nat.card {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} ≤
      Nat.card (Fin 120) := by
    rw [generatedOctad_short_support_card]
    simp
  obtain ⟨p, hp⟩ := hi.bijective_of_nat_card_le hc |>.surjective ⟨r, hr⟩
  exact ⟨p, congrArg Subtype.val hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
