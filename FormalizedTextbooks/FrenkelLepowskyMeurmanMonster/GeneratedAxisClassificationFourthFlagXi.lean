/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairPhaseCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransport

/-! An actual signed three-bases element preserving the distinguished fourth-axis flag.
The sign conjugation compensates the preferred minus pair and the exact order-three Xi matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine code label thirty-two has opposite signs at the pair endpoints. -/
def generatedFourthFlagXiSign : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 32), ⟨_, rfl⟩⟩

/-- The signed correction of the actual physical three-bases isometry. -/
noncomputable def generatedFourthFlagNormalizedXi : leechIsomSubgroup :=
  golaySignIsometry generatedFourthFlagXiSign * generatedFourthFlagCorrectionLeech *
    co1XiIsometry * golaySignIsometry generatedFourthFlagXiSign

/-- Integral coordinates of the selected preferred minus pair. -/
def generatedFourthFlagPairIntegral : Fin 24 → ℤ := fun i =>
  4 * (if i = 8 then 1 else 0) - 4 * (if i = 11 then 1 else 0)

/-- The selected actual preferred short vector has these integral coordinates. -/
theorem generatedFourth_flag_pair_integral :
    griessShortIntegral generatedFourthFlagShort = generatedFourthFlagPairIntegral := by
  funext i
  simp only [generatedFourthFlagShort, generatedFourthFlagSign,
    generatedFourth_pair_phase_zero, ite_true, griessShortIntegral,
    generatedFourthPairInput_coordinates, generatedFourthFlagPairIntegral]
  norm_num
  split_ifs <;> norm_num

/-- Exact signed numerator certificate for the preferred pair and the actual Xi orientation. -/
theorem generatedFourth_flag_xi_pair_certificate : ∀ i : Fin 24,
    golayIntegerSign generatedFourthFlagXiSign.val
      (golayIntegerPermute generatedFourthFlagCorrectionPermutation
        (co1XiNumerator *ᵥ golayIntegerSign generatedFourthFlagXiSign.val
          generatedFourthFlagPairIntegral)) i =
      -2 * generatedFourthFlagPairIntegral i := by
  decide +kernel

/-- The actual corrected isometry negates the selected physical short vector integrally. -/
theorem generatedFourth_flag_xi_integral :
    (leechIntegralAction generatedFourthFlagNormalizedXi
      (griessShortLatticeVector generatedFourthFlagShort)).val =
      -griessShortIntegral generatedFourthFlagShort := by
  let u := griessShortLatticeVector generatedFourthFlagShort
  let v := leechIntegralAction (golaySignIsometry generatedFourthFlagXiSign) u
  let w := leechIntegralAction co1XiIsometry v
  have hv : v.val = golayIntegerSign generatedFourthFlagXiSign.val
      generatedFourthFlagPairIntegral := by
    rw [show v = leechIntegralAction (golaySignIsometry generatedFourthFlagXiSign) u from rfl,
      leechIntegralAction_golaySign]
    change golayIntegerSign _ (griessShortIntegral generatedFourthFlagShort) = _
    rw [generatedFourth_flag_pair_integral]
  have hd := co1Xi_integral_double v
  rw [hv] at hd
  funext i
  have he := congrFun hd (generatedFourthFlagCorrectionCoordinates i)
  change 2 * w.val (generatedFourthFlagCorrectionCoordinates i) = _ at he
  have hc := generatedFourth_flag_xi_pair_certificate i
  change (if generatedFourthFlagXiSign.val i = 0 then
      (co1XiNumerator *ᵥ golayIntegerSign generatedFourthFlagXiSign.val
        generatedFourthFlagPairIntegral) (generatedFourthFlagCorrectionCoordinates i)
    else -(co1XiNumerator *ᵥ golayIntegerSign generatedFourthFlagXiSign.val
        generatedFourthFlagPairIntegral) (generatedFourthFlagCorrectionCoordinates i)) = _ at hc
  change (leechIntegralAction
    (golaySignIsometry generatedFourthFlagXiSign * generatedFourthFlagCorrectionLeech *
      co1XiIsometry * golaySignIsometry generatedFourthFlagXiSign) u).val i = _
  rw [map_mul, map_mul, map_mul]
  change (leechIntegralAction (golaySignIsometry generatedFourthFlagXiSign)
    (leechIntegralAction generatedFourthFlagCorrectionLeech w)).val i = _
  rw [leechIntegralAction_golaySign]
  change (if generatedFourthFlagXiSign.val i = 0 then
    (leechIntegralAction generatedFourthFlagCorrectionLeech w).val i else
      -(leechIntegralAction generatedFourthFlagCorrectionLeech w).val i) = _
  rw [show generatedFourthFlagCorrectionLeech =
      golayPermutationIsometry generatedFourthFlagCorrectionGolay from rfl,
    leechIntegralAction_golayPermutation]
  change (if generatedFourthFlagXiSign.val i = 0 then
    w.val (generatedFourthFlagCorrectionCoordinates i) else
    -w.val (generatedFourthFlagCorrectionCoordinates i)) = _
  rw [generatedFourth_flag_pair_integral]
  change (if generatedFourthFlagXiSign.val i = 0 then
    w.val (generatedFourthFlagCorrectionCoordinates i) else
    -w.val (generatedFourthFlagCorrectionCoordinates i)) = -generatedFourthFlagPairIntegral i
  split_ifs at hc ⊢ <;> omega

/-- The corrected actual Xi negates the genuine physical preferred short vector. -/
theorem generatedFourth_flag_xi_short_vector :
    generatedFourthFlagNormalizedXi.val (griessShortVector generatedFourthFlagShort) =
      -griessShortVector generatedFourthFlagShort := by
  have h := leechIntegralAction_embedding generatedFourthFlagNormalizedXi
    (griessShortLatticeVector generatedFourthFlagShort)
  rw [generatedFourth_flag_xi_integral, map_neg] at h
  exact h.symm

/-- The corrected actual Xi fixes the genuine short-line label. -/
theorem generatedFourth_flag_xi_short_label :
    griessShortPermutation generatedFourthFlagNormalizedXi generatedFourthFlagShort =
      generatedFourthFlagShort := by
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector generatedFourthFlagNormalizedXi
      generatedFourthFlagShort with h | h
  · exact Or.inr (h.symm.trans generatedFourth_flag_xi_short_vector)
  · have he := h.symm.trans generatedFourth_flag_xi_short_vector
    exact Or.inl (neg_injective he)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
