/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagSpatialData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagXiPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Compatibility

/-! A genuine local lift of a signed three-bases generator of the fourth physical flag. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The existing full-phase y82 sign lifts normalize the original triality orientation. -/
noncomputable def generatedFourthFlagNormalizedLift : localFiberSubgroup :=
  monsterSourceY82Fiber * generatedFourthFlagCorrectionFiber * xiSpinLocalFiber *
    monsterSourceY82Fiber

/-- Exact signed numerator certificate for the preferred pair and the actual Xi orientation. -/
theorem generatedFourth_flag_lift_pair_certificate : ∀ i : Fin 24,
    golayIntegerSign monsterSourceY82SignCode.val
      (golayIntegerPermute generatedFourthFlagCorrectionPermutation
        (co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val
          generatedFourthFlagPairIntegral)) i =
      -2 * generatedFourthFlagPairIntegral i := by
  decide +kernel

/-- The actual corrected isometry negates the selected physical short vector integrally. -/
theorem generatedFourth_flag_lift_integral :
    (leechIntegralAction generatedFourthFlagNormalizedLift.val.2
      (griessShortLatticeVector generatedFourthFlagShort)).val =
      -griessShortIntegral generatedFourthFlagShort := by
  let u := griessShortLatticeVector generatedFourthFlagShort
  let v := leechIntegralAction (golaySignIsometry monsterSourceY82SignCode) u
  let w := leechIntegralAction co1XiIsometry v
  have hv : v.val = golayIntegerSign monsterSourceY82SignCode.val
      generatedFourthFlagPairIntegral := by
    rw [show v = leechIntegralAction (golaySignIsometry monsterSourceY82SignCode) u from rfl,
      leechIntegralAction_golaySign]
    change golayIntegerSign _ (griessShortIntegral generatedFourthFlagShort) = _
    rw [generatedFourth_flag_pair_integral]
  have hd := co1Xi_integral_double v
  rw [hv] at hd
  funext i
  have he := congrFun hd (generatedFourthFlagCorrectionCoordinates i)
  change 2 * w.val (generatedFourthFlagCorrectionCoordinates i) = _ at he
  have hc := generatedFourth_flag_lift_pair_certificate i
  change (if monsterSourceY82SignCode.val i = 0 then
      (co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val
        generatedFourthFlagPairIntegral) (generatedFourthFlagCorrectionCoordinates i)
    else -(co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val
        generatedFourthFlagPairIntegral) (generatedFourthFlagCorrectionCoordinates i)) = _ at hc
  change (leechIntegralAction
    (golaySignIsometry monsterSourceY82SignCode * generatedFourthFlagCorrectionLeech *
      co1XiIsometry * golaySignIsometry monsterSourceY82SignCode) u).val i = _
  rw [map_mul, map_mul, map_mul]
  change (leechIntegralAction (golaySignIsometry monsterSourceY82SignCode)
    (leechIntegralAction generatedFourthFlagCorrectionLeech w)).val i = _
  rw [leechIntegralAction_golaySign]
  change (if monsterSourceY82SignCode.val i = 0 then
    (leechIntegralAction generatedFourthFlagCorrectionLeech w).val i else
      -(leechIntegralAction generatedFourthFlagCorrectionLeech w).val i) = _
  rw [show generatedFourthFlagCorrectionLeech =
      golayPermutationIsometry generatedFourthFlagCorrectionGolay from rfl,
    leechIntegralAction_golayPermutation]
  change (if monsterSourceY82SignCode.val i = 0 then
    w.val (generatedFourthFlagCorrectionCoordinates i) else
    -w.val (generatedFourthFlagCorrectionCoordinates i)) = _
  rw [generatedFourth_flag_pair_integral]
  change (if monsterSourceY82SignCode.val i = 0 then
    w.val (generatedFourthFlagCorrectionCoordinates i) else
    -w.val (generatedFourthFlagCorrectionCoordinates i)) = -generatedFourthFlagPairIntegral i
  split_ifs at hc ⊢ <;> omega

/-- The corrected actual Xi negates the genuine physical preferred short vector. -/
theorem generatedFourth_flag_lift_short_vector :
    generatedFourthFlagNormalizedLift.val.2.val (griessShortVector generatedFourthFlagShort) =
      -griessShortVector generatedFourthFlagShort := by
  have h := leechIntegralAction_embedding generatedFourthFlagNormalizedLift.val.2
    (griessShortLatticeVector generatedFourthFlagShort)
  rw [generatedFourth_flag_lift_integral, map_neg] at h
  exact h.symm

/-- The corrected actual Xi fixes the genuine short-line label. -/
theorem generatedFourth_flag_lift_short_label :
    griessShortPermutation generatedFourthFlagNormalizedLift.val.2 generatedFourthFlagShort =
      generatedFourthFlagShort := by
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector generatedFourthFlagNormalizedLift.val.2
      generatedFourthFlagShort with h | h
  · exact Or.inr (h.symm.trans generatedFourth_flag_lift_short_vector)
  · have he := h.symm.trans generatedFourth_flag_lift_short_vector
    exact Or.inl (neg_injective he)


private theorem preserves_mul (c : Fin 24 → ZMod 2) (g h : leechIsomSubgroup)
    (hg : generatedOctadPreserves c g) (hh : generatedOctadPreserves c h) :
    generatedOctadPreserves c (g * h) := by
  intro u
  rw [map_mul, LinearEquiv.mul_apply]
  exact (hg _).trans (hh u)

/-- The actual local lift preserves the entire selected integral section. -/
theorem generatedFourth_flag_lift_section_preserves :
    generatedOctadPreserves (golayOctadWord generatedFourthFlagOctad)
      generatedFourthFlagNormalizedLift.val.2 := by
  have hc : golayOctadWord generatedFourthFlagOctad =
      golayEncoder (golayLabelCoefficients 14) := by
    unfold golayOctadWord
    rw [generatedFourthFlagOctad_label]
  rw [hc]
  have hp : generatedOctadPreserves (golayEncoder (golayLabelCoefficients 14))
      generatedFourthFlagCorrectionLeech := by
    intro u
    exact generatedOctadSupported_permutation _ _ generatedFourthFlagCorrectionGolay
      generatedFourthFlagCorrection_word u
  have hs := generatedAxisE8_sign_preserves
    (golayEncoder (golayLabelCoefficients 14)) monsterSourceY82SignCode
  change generatedOctadPreserves _
    (golaySignIsometry monsterSourceY82SignCode * generatedFourthFlagCorrectionLeech *
      co1XiIsometry * golaySignIsometry monsterSourceY82SignCode)
  exact preserves_mul _ _ _
    (preserves_mul _ _ _ (preserves_mul _ _ _ hs hp)
      generatedFourth_flag_xi_section_preserves) hs

/-- The actual spatial component belongs to the counted fourth flag stabilizer. -/
theorem generatedFourth_flag_lift_mem :
    generatedFourthFlagNormalizedLift.val.2 ∈ generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort := by
  rw [generatedAxisE8ShortFlagStabilizer_mem]
  exact ⟨generatedAxisE8_preserving_image _ _ generatedFourth_flag_lift_section_preserves,
    generatedFourth_flag_lift_short_label⟩

/-- The literal full extraspecial image of the actual normalized lift. -/
noncomputable def generatedFourthFlagNormalizedQImage (q : Q) : Q :=
  monsterSourceY82Image (generatedFourthFlagLiftQImage
    (xiSpinGImage (xiSpinGammaImage (monsterSourceY82Image q))))

/-- The genuine spin conjugation retains every original central phase. -/
theorem generatedFourth_flag_lift_conjugation (q : Q) :
    spinConjugation generatedFourthFlagNormalizedLift.val.1 q =
      generatedFourthFlagNormalizedQImage q := by
  change spinConjugation
    (monsterSourceY82Spin * generatedFourthFlagLiftSpin * xiSpinHolomorph *
      monsterSourceY82Spin) q = _
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterSourceY82Spin_conjugation, xiSpinHolomorph_conjugation,
    generatedFourth_flag_lift_spin_conjugation, monsterSourceY82Spin_conjugation]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
