/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQExact

/-! Actual original generator attainment, conditional on twelve explicit whole-axis fixation equations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The original first ten spatial candidates are precisely the genuine Mathieu strong generators. -/
theorem generatedRootEight_generator_spatial_mathieu (j : Fin 10) :
    generatedRootEightGeneratorSpatial (Fin.castAdd 2 j) =
      golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator j) := by
  simp only [generatedRootEightGeneratorSpatial, Fin.val_castAdd, j.isLt, dite_true]

/-- The eleventh spatial candidate is the literal original flag mover. -/
theorem generatedRootEight_generator_spatial_mover :
    generatedRootEightGeneratorSpatial 10 = leechNormSixHS100PointMover := by
  simp [generatedRootEightGeneratorSpatial]

/-- The twelfth spatial candidate is the literal original mate-orientation word. -/
theorem generatedRootEight_generator_spatial_mate :
    generatedRootEightGeneratorSpatial 11 = leechNormSixHS100MateOrientation := by
  simp [generatedRootEightGeneratorSpatial]

/-- Any actual Conway subgroup containing the twelve original spatial words contains the entire
canonical positive-root two-companion group. -/
theorem generatedRootEight_generators_contain_mate_group (S : Subgroup leechIsomSubgroup)
    (hS : ∀ j : Fin 12, generatedRootEightGeneratorSpatial j ∈ S) :
    leechNormSixHS100MateGroup ≤ S := by
  let F := leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion
  have hM : leechNormSixHS100PairPointStabilizer.map F.subtype ≤ S := by
    rw [← leechNormSixHS100Mathieu_generated_in_conway]
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    change golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator j) ∈ S
    simpa only [generatedRootEight_generator_spatial_mathieu] using hS (Fin.castAdd 2 j)
  have hm : leechNormSixHS100PointMover ∈ S := by
    simpa only [generatedRootEight_generator_spatial_mover] using hS 10
  have hf : F ≤ S := by
    have h := congrArg (fun K : Subgroup F => K.map F.subtype)
      leechNormSixHS100PointMover_generates
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top,
      Subgroup.range_subtype] at h
    change leechNormSixHS100PairPointStabilizer.map F.subtype ⊔
      Subgroup.zpowers leechNormSixHS100PointMover = F at h
    rw [← h]
    exact sup_le hM (Subgroup.zpowers_le.mpr hm)
  rw [← leechNormSixHS100MateGroup_generates]
  apply sup_le hf
  apply Subgroup.zpowers_le.mpr
  simpa only [generatedRootEight_generator_spatial_mate] using hS 11

/-- The actual positive-root two-companion group maps to the original root-eight Conway coordinates. -/
def generatedRootEightMateQuotient : leechNormSixHS100MateGroup →* Co1 :=
  generatedRootEightCanonicalQuotientConjugation.comp leechNormSixHS100MateGroup.subtype

/-- The canonical positive-root group has no central-sign collapse in the genuine Conway quotient. -/
theorem generatedRootEight_mate_quotient_injective :
    Function.Injective generatedRootEightMateQuotient := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  let p := projH generatedFifthRootEightCanonicalLocal
  have h : p⁻¹ * QuotientGroup.mk' signsSubgroup g.val * p = 1 := hg
  have hq : QuotientGroup.mk' signsSubgroup g.val = 1 := by
    have hh := congrArg (fun z : Co1 => p * z * p⁻¹) h
    simpa [mul_assoc] using hh
  have hs : g.val ∈ signsSubgroup := by
    have hker : g.val ∈ (QuotientGroup.mk' signsSubgroup).ker := hq
    simpa only [QuotientGroup.ker_mk'] using hker
  rcases hs with hi | hn
  · apply Subtype.ext
    exact Subtype.ext hi
  · have he := leechIntegralAction_embedding g.val leechNormSixHS100Root
    rw [g.property.1, hn] at he
    have he0 := congrFun he 0
    simp only [Pi.neg_apply] at he0
    have hz : leechCoordinateEmbedding leechNormSixHS100Root.val 0 ≠ 0 := by
      change (4 : ℝ) / Real.sqrt 8 ≠ 0
      exact div_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    exact False.elim (hz (by linarith))

/-- The actual attained image of the canonical positive-root group has88704000 elements. -/
theorem generatedRootEight_mate_quotient_range_card :
    Nat.card generatedRootEightMateQuotient.range = 88704000 := by
  rw [← Nat.card_congr
    (MonoidHom.ofInjective generatedRootEight_mate_quotient_injective).toEquiv]
  exact leechNormSixHS100MateGroup_card

/-- Whole-axis fixation of the twelve explicit original local candidates attains the entire
required Conway image; no matrix-only or scalar-witness hypothesis is substituted. -/
theorem generatedRootEight_generator_fixation_projected_order
    (hfix : ∀ j : Fin 12, rhoLocal (generatedRootEightGeneratorCandidate j)
      generatedFifthRootEightAxis = generatedFifthRootEightAxis) :
    Nat.card generatedFifthRootEightProjectedAxisStabilizer = 88704000 := by
  let S := generatedFifthRootEightProjectedAxisStabilizer.comap
    generatedRootEightCanonicalQuotientConjugation
  have hS : ∀ j : Fin 12, generatedRootEightGeneratorSpatial j ∈ S := by
    intro j
    change generatedRootEightCanonicalQuotientConjugation (generatedRootEightGeneratorSpatial j) ∈
      generatedFifthRootEightProjectedAxisStabilizer
    rw [← generatedRootEight_generator_candidate_projection]
    exact ⟨⟨generatedRootEightGeneratorCandidate j, hfix j⟩, rfl⟩
  have hM := generatedRootEight_generators_contain_mate_group S hS
  have hr : generatedRootEightMateQuotient.range ≤ generatedFifthRootEightProjectedAxisStabilizer := by
    rintro _ ⟨g, rfl⟩
    exact hM g.property
  let : Finite Co1 := co1_finite
  apply Nat.le_antisymm
  · exact generatedFifthRootEight_projected_card_le_spatial.trans_eq
      generatedFifthRootEight_Co1_spatial_stabilizer_card
  · rw [← generatedRootEight_mate_quotient_range_card]
    exact Subgroup.card_le_of_le hr

/-- The same twelve complete original fixation equations give the exact full local-axis order. -/
theorem generatedRootEight_generator_fixation_local_order
    (hfix : ∀ j : Fin 12, rhoLocal (generatedRootEightGeneratorCandidate j)
      generatedFifthRootEightAxis = generatedFifthRootEightAxis) :
    Nat.card generatedFifthRootEightLocalAxisStabilizer = 177408000 := by
  exact generatedFifthRootEight_local_order_iff_projected_order.mpr
    (generatedRootEight_generator_fixation_projected_order hfix)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
