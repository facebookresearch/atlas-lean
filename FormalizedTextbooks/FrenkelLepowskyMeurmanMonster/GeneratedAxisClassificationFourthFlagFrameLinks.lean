/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagLiftGeometry

/-! Actual integral frame links supplied by the normalized fourth flag generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Two actual lattice witnesses for the coordinate and four-coordinate frame patterns. -/
def generatedFourthFlagFrameInput (k : Fin 2) : leechIntegral :=
  griessShortLatticeVector generatedFourthFlagShort +
    if k = 0 then griessShortLatticeVector (Sum.inl (1, griessPairIndex 8 11 (by decide)))
    else griessShortLatticeVector (Sum.inl (1, griessPairIndex 4 9 (by decide)))

/-- Literal integral coordinates of the two actual frame witnesses. -/
def generatedFourthFlagFrameInputCoordinates : Fin 2 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Positive-incidence representatives of the actual normalized-generator images. -/
def generatedFourthFlagFrameOutputCoordinates : Fin 2 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 4, 4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 2, -2, -2, 2, -2, -2, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

private theorem pair_plus_integral (a b : Fin 24) (hab : a < b) :
    griessShortIntegral (Sum.inl (1, griessPairIndex a b (ne_of_lt hab))) =
      fun i => 4 * (if i = a then 1 else 0) + 4 * (if i = b then 1 else 0) := by
  funext i
  simp only [griessShortIntegral, griessPairIndex_coordinates, hab, ite_true]
  split_ifs <;> norm_num <;> omega

/-- The literal input arrays are genuine lattice vectors, built from actual short vectors. -/
theorem generatedFourth_flag_frame_input_coordinates (k : Fin 2) :
    (generatedFourthFlagFrameInput k).val = generatedFourthFlagFrameInputCoordinates k := by
  have hk : k = 0 ∨ k = 1 := by
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hk with rfl | rfl
  · change griessShortIntegral generatedFourthFlagShort +
      griessShortIntegral (Sum.inl (1, griessPairIndex 8 11 (by decide))) = _
    rw [generatedFourth_flag_pair_integral, pair_plus_integral 8 11 (by decide)]
    funext i
    fin_cases i <;> norm_num [generatedFourthFlagPairIntegral,
      generatedFourthFlagFrameInputCoordinates]
  · change griessShortIntegral generatedFourthFlagShort +
      griessShortIntegral (Sum.inl (1, griessPairIndex 4 9 (by decide))) = _
    rw [generatedFourth_flag_pair_integral, pair_plus_integral 4 9 (by decide)]
    funext i
    fin_cases i <;> norm_num [generatedFourthFlagPairIntegral,
      generatedFourthFlagFrameInputCoordinates]

/-- The complete doubled integral action of the original normalized flag lift. -/
theorem generatedFourth_flag_lift_integral_double (u : leechIntegral) :
    (2 : ℤ) • (leechIntegralAction generatedFourthFlagNormalizedLift.val.2 u).val =
      golayIntegerSign monsterSourceY82SignCode.val
        (golayIntegerPermute generatedFourthFlagCorrectionPermutation
          (co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val u.val)) := by
  let v := leechIntegralAction (golaySignIsometry monsterSourceY82SignCode) u
  let w := leechIntegralAction co1XiIsometry v
  have hd := co1Xi_integral_double v
  rw [show v.val = golayIntegerSign monsterSourceY82SignCode.val u.val from
    leechIntegralAction_golaySign _ u] at hd
  funext i
  have he := congrFun hd (generatedFourthFlagCorrectionCoordinates i)
  change 2 * w.val (generatedFourthFlagCorrectionCoordinates i) = _ at he
  change 2 * (leechIntegralAction
    (golaySignIsometry monsterSourceY82SignCode * generatedFourthFlagCorrectionLeech *
      co1XiIsometry * golaySignIsometry monsterSourceY82SignCode) u).val i = _
  rw [map_mul, map_mul, map_mul]
  change 2 * (leechIntegralAction (golaySignIsometry monsterSourceY82SignCode)
    (leechIntegralAction generatedFourthFlagCorrectionLeech w)).val i = _
  rw [leechIntegralAction_golaySign]
  rw [show generatedFourthFlagCorrectionLeech =
    golayPermutationIsometry generatedFourthFlagCorrectionGolay from rfl,
    leechIntegralAction_golayPermutation]
  change 2 * (if monsterSourceY82SignCode.val i = 0 then
      w.val (generatedFourthFlagCorrectionCoordinates i) else
        -w.val (generatedFourthFlagCorrectionCoordinates i)) =
    (if monsterSourceY82SignCode.val i = 0 then
      (co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val u.val)
        (generatedFourthFlagCorrectionCoordinates i) else
      -(co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val u.val)
        (generatedFourthFlagCorrectionCoordinates i))
  split_ifs <;> omega

/-- Exact signed coordinate certificates for both original-generator frame links. -/
theorem generatedFourth_flag_frame_link_certificate : ∀ k : Fin 2, ∀ i : Fin 24,
    golayIntegerSign monsterSourceY82SignCode.val
      (golayIntegerPermute generatedFourthFlagCorrectionPermutation
        (co1XiNumerator *ᵥ golayIntegerSign monsterSourceY82SignCode.val
          (generatedFourthFlagFrameInputCoordinates k))) i =
      -2 * generatedFourthFlagFrameOutputCoordinates k i := by
  decide +kernel

/-- The actual normalized generator connects coordinate, four-coordinate and six-plus-two frames. -/
theorem generatedFourth_flag_frame_links (k : Fin 2) :
    -(leechIntegralAction generatedFourthFlagNormalizedLift.val.2
      (generatedFourthFlagFrameInput k)).val = generatedFourthFlagFrameOutputCoordinates k := by
  have h := generatedFourth_flag_lift_integral_double (generatedFourthFlagFrameInput k)
  rw [generatedFourth_flag_frame_input_coordinates] at h
  funext i
  have hi := congrFun h i
  have hc := generatedFourth_flag_frame_link_certificate k i
  change 2 * (leechIntegralAction generatedFourthFlagNormalizedLift.val.2
    (generatedFourthFlagFrameInput k)).val i = _ at hi
  change -(leechIntegralAction generatedFourthFlagNormalizedLift.val.2
    (generatedFourthFlagFrameInput k)).val i = _
  omega

/-- All four literal witnesses have norm eight, positive incidence and actual octad support. -/
theorem generatedFourth_flag_frame_link_norms : ∀ k : Fin 2,
    leechSquareSum (generatedFourthFlagFrameInputCoordinates k) = 64 ∧
      leechSquareSum (generatedFourthFlagFrameOutputCoordinates k) = 64 ∧
      (∑ i, generatedFourthFlagFrameInputCoordinates k i * generatedFourthFlagPairIntegral i) = 32 ∧
      (∑ i, generatedFourthFlagFrameOutputCoordinates k i * generatedFourthFlagPairIntegral i) =
        32 ∧
      ∀ i : Fin 24, ¬Nat.testBit 0xff0 i.val →
        generatedFourthFlagFrameInputCoordinates k i = 0 ∧
          generatedFourthFlagFrameOutputCoordinates k i = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
