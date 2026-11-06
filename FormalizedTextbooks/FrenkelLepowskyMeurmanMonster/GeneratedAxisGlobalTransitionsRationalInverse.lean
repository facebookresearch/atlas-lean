/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsInversePairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsInverseFourier

/-! Direct complete original inverse coordinates avoid repeated octad Fourier summation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original inverse physical matrix has the preferred pair difference. -/
def generatedAxisGlobalInverseMatrixQ (a : GeneratedAxisGlobalRationalPacket)
    (i j : Fin 24) : ℚ :=
  if i = j then a.1 i i else
    (a.2.1 (Sum.inl (0, generatedAxisGlobalFinitePairIndex i j)) -
      a.2.1 (Sum.inl (1, generatedAxisGlobalFinitePairIndex i j))) / 2

/-- All three actual inverse short families, including the original transpose Fourier sum. -/
def generatedAxisGlobalInverseShortQ (a : GeneratedAxisGlobalRationalPacket) : GriessShortIndex → ℚ
  | Sum.inl (s, p) =>
      if s = 0 then
        a.1 (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
          (a.2.1 (Sum.inl (0, p)) + a.2.1 (Sum.inl (1, p))) / 2
      else a.1 (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 -
        (a.2.1 (Sum.inl (0, p)) + a.2.1 (Sum.inl (1, p))) / 2
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, (trialityIntegerMatrix f e : ℚ) / 8 *
        a.2.1 (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, j)) =>
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
        (a.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) j -
          a.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) j) / 2

/-- Every inverse scaled tensor coefficient keeps the original odd-short and tensor-sum terms. -/
def generatedAxisGlobalInverseTensorQ (a : GeneratedAxisGlobalRationalPacket)
    (t : SpinIndex) (j : Fin 24) : ℚ :=
  let d := generatedAxisGlobalSpinLabelLow (generatedAxisGlobalSpinLabel t)
  let e : ℚ := generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  let z : ℚ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  e * a.2.1 (Sum.inr (Sum.inr (d, j))) +
    (generatedAxisGlobalIntSign (t 11) : ℚ) * e * z *
      (a.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) j +
        a.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) j) / 2

/-- The full direct inverse packet retains every actual source constituent. -/
def generatedAxisGlobalRationalInverse (a : GeneratedAxisGlobalRationalPacket) :
    GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalInverseMatrixQ a,
    (generatedAxisGlobalInverseShortQ a, generatedAxisGlobalInverseTensorQ a))

private theorem inverse_code_low (d : Fin 2048) :
    generatedAxisGlobalSpinLabelLow
      (generatedAxisGlobalSpinLabel (golayLabelCoefficients ⟨d.val, by omega⟩)) = d := by
  rw [generatedAxisGlobalSpinLabel_coeff]
  apply Fin.ext
  change d.val % 2048 = d.val
  omega

private theorem inverse_code_high (d : Fin 2048) :
    generatedAxisGlobalSpinLabelLow
      (generatedAxisGlobalSpinLabel (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) = d := by
  rw [generatedAxisGlobalSpinLabel_coeff]
  apply Fin.ext
  change (d.val + 2048) % 2048 = d.val
  omega

set_option maxHeartbeats 2000000 in
/-- Two original forward XYZ operations give the complete direct inverse odd-short coefficient. -/
theorem generatedAxisGlobalRationalInverse_odd (a : GeneratedAxisGlobalRationalPacket)
    (d : Fin 2048) (j : Fin 24) :
    (generatedAxisGlobalRationalTriality (generatedAxisGlobalRationalTriality a)).2.1
      (Sum.inr (Sum.inr (d, j))) =
        generatedAxisGlobalInverseShortQ a (Sum.inr (Sum.inr (d, j))) := by
  simp only [generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityShortQ,
    generatedAxisGlobalTrialityScaledTensorQ, inverse_code_low, inverse_code_high,
    golayLabel_low_last, golayLabel_high_last, generatedAxisGlobalInverseShortQ]
  norm_num [generatedAxisGlobalIntSign]
  split_ifs <;> ring

set_option maxHeartbeats 2000000 in
/-- Two original forward XYZ operations give every complete direct inverse scaled tensor coefficient. -/
theorem generatedAxisGlobalRationalInverse_tensor (a : GeneratedAxisGlobalRationalPacket)
    (t : SpinIndex) (j : Fin 24) :
    (generatedAxisGlobalRationalTriality (generatedAxisGlobalRationalTriality a)).2.2 t j =
      generatedAxisGlobalInverseTensorQ a t j := by
  simp only [generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityScaledTensorQ,
    generatedAxisGlobalTrialityShortQ, inverse_code_low, inverse_code_high,
    golayLabel_low_last, golayLabel_high_last, generatedAxisGlobalInverseTensorQ]
  norm_num [generatedAxisGlobalIntSign]
  split_ifs <;> ring

set_option maxHeartbeats 2000000 in
/-- The full direct rational inverse agrees with the genuine original inverse action. -/
theorem generatedAxisGlobalRationalInverse_actual (x : GriessSpace)
    (a : GeneratedAxisGlobalRationalPacket)
    (ha : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a) :
    griessConwayEncode (sExtra.symm x) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalRationalInverse a) := by
  have h2 := generatedAxisGlobalRationalInverse_of_actual x a ha
  apply Prod.ext
  · ext i j
    rw [generatedAxisGlobal_inverse_matrix_coordinate, ha]
    simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
      generatedAxisGlobalInverseMatrixQ, Matrix.map_apply]
    split_ifs with h
    · rfl
    · rw [generatedAxisGlobalFinitePairIndex_actual i j h]
      simp
  · apply Prod.ext
    · funext r
      rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
      · fin_cases s
        · change (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inl (0, p)) = _
          rw [generatedAxisGlobal_inverse_pair_zero_coordinate, ha]
          simp [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
            generatedAxisGlobalInverseShortQ, generatedAxisGlobalPairCoordinates_actual]
        · change (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inl (1, p)) = _
          rw [generatedAxisGlobal_inverse_pair_one_coordinate, ha]
          simp [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
            generatedAxisGlobalInverseShortQ, generatedAxisGlobalPairCoordinates_actual]
      · rw [generatedAxisGlobal_inverse_octad_coordinate, ha]
        simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
          generatedAxisGlobalInverseShortQ, trialityRealMatrix, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
          Rat.cast_intCast, Rat.cast_ofNat, one_div]
        apply Finset.sum_congr rfl
        intro f _
        change (8 : ℝ)⁻¹ * (trialityIntegerMatrix f e : ℝ) *
          (a.2.1 (Sum.inr (Sum.inl (o, f))) : ℝ) = _
        ring
      · have hh := congrArg (fun y : ConwayRawSpace => y.2.1 (Sum.inr (Sum.inr (d, j)))) h2
        simpa only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
          generatedAxisGlobalRationalInverse_odd] using hh
    · funext t j
      have hh := congrArg (fun y : ConwayRawSpace => y.2.2 t j) h2
      simpa only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
        generatedAxisGlobalRationalInverse_tensor] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
