/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTrialityTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFinitePairIndex

/-! Complete rational coordinate packets for the genuine original triality action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A rational physical matrix, short constituent and square-root-scaled tensor constituent. -/
abbrev GeneratedAxisGlobalRationalPacket :=
  Matrix (Fin 24) (Fin 24) ℚ ×
    ((GriessShortIndex → ℚ) × (SpinIndex → Fin 24 → ℚ))

/-- Real coordinates of a complete rational packet with the original tensor normalization. -/
def generatedAxisGlobalRationalPacketReal (a : GeneratedAxisGlobalRationalPacket) : ConwayRawSpace :=
  (a.1.map (Rat.castHom ℝ),
    ((fun r => (a.2.1 r : ℝ)), fun t j => (a.2.2 t j : ℝ) / Real.sqrt 2))

/-- The entire rational forward matrix retains both original preferred pair coefficients. -/
def generatedAxisGlobalTrialityMatrixQ (a : GeneratedAxisGlobalRationalPacket)
    (i j : Fin 24) : ℚ :=
  if i = j then a.1 i i else
    (a.2.1 (Sum.inl (0, generatedAxisGlobalFinitePairIndex i j)) +
      a.2.1 (Sum.inl (1, generatedAxisGlobalFinitePairIndex i j))) / 2

/-- The full rational short formula includes each pair, octad Fourier and odd coefficient. -/
def generatedAxisGlobalTrialityShortQ (a : GeneratedAxisGlobalRationalPacket) : GriessShortIndex → ℚ
  | Sum.inl (s, p) =>
      if s = 0 then
        a.1 (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
          (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2
      else
        (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2 -
          a.1 (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 *
        a.2.1 (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, i)) =>
      (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) *
        (a.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          a.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / 2

/-- Every constituent of the complete original forward source operator is rational. -/
def generatedAxisGlobalRationalTriality (a : GeneratedAxisGlobalRationalPacket) :
    GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalTrialityMatrixQ a,
    (generatedAxisGlobalTrialityShortQ a,
      generatedAxisGlobalTrialityScaledTensorQ a.2.1 a.2.2))

set_option maxHeartbeats 2000000 in
/-- The full rational packet acts exactly as the original real triality formula. -/
theorem generatedAxisGlobalRationalTriality_actual (a : GeneratedAxisGlobalRationalPacket) :
    generatedAxisGlobalRawTrialityFormula (generatedAxisGlobalRationalPacketReal a) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalRationalTriality a) := by
  apply Prod.ext
  · ext i j
    simp only [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityMatrix,
      generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalTriality,
      generatedAxisGlobalTrialityMatrixQ, Matrix.map_apply]
    split_ifs with h
    · rfl
    · rw [generatedAxisGlobalFinitePairIndex_actual i j h]
      simp [map_add]
  · apply Prod.ext
    · funext r
      rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
      · simp only [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
          generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalTriality,
          generatedAxisGlobalTrialityShortQ, generatedAxisGlobalPairCoordinates_actual, Matrix.map_apply]
        split_ifs <;> simp
      · simp only [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
          generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalTriality,
          generatedAxisGlobalTrialityShortQ, trialityRealMatrix, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
          Rat.cast_intCast, Rat.cast_ofNat, one_div]
        apply Finset.sum_congr rfl
        intro f _
        change (8 : ℝ)⁻¹ * (trialityIntegerMatrix e f : ℝ) *
          (a.2.1 (Sum.inr (Sum.inl (o, f))) : ℝ) = _
        ring
      · simp only [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
          generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalTriality,
          generatedAxisGlobalTrialityShortQ, Rat.cast_div, Rat.cast_mul, Rat.cast_add,
          Rat.cast_intCast, Rat.cast_ofNat, generatedAxisGlobalIntSign_real]
        field_simp
        rw [show Real.sqrt 2 ^ 2 = (2 : ℝ) from Real.sq_sqrt (by norm_num)]
        ring
    · funext t j
      change generatedAxisGlobalRawTrialityTensor (generatedAxisGlobalRationalPacketReal a) t j = _
      simp only [generatedAxisGlobalRawTrialityTensor, generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityScaledTensorQ,
        trialityYTensor, generatedAxisGlobalSpinLabelLow_dictionary,
        generatedAxisGlobalSpinLabel_decode, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_sub, Rat.cast_intCast, generatedAxisGlobalIntSign_real,
        apply_ite, Rat.cast_neg, Rat.cast_one, ↓reduceIte]
      ring

/-- An actual full source packet gives the entire original forward transition. -/
theorem generatedAxisGlobalRationalTriality_of_actual (x : GriessSpace)
    (a : GeneratedAxisGlobalRationalPacket)
    (ha : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a) :
    griessConwayEncode (sExtra x) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalRationalTriality a) := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, ha,
    generatedAxisGlobalRationalTriality_actual]

/-- The actual full inverse transition is exactly two complete rational source operations. -/
theorem generatedAxisGlobalRationalInverse_of_actual (x : GriessSpace)
    (a : GeneratedAxisGlobalRationalPacket)
    (ha : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a) :
    griessConwayEncode (sExtra.symm x) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalTriality (generatedAxisGlobalRationalTriality a)) := by
  rw [generatedAxisGlobalRawInverseFormula_actual, ha,
    generatedAxisGlobalRawInverseFormula, generatedAxisGlobalRationalTriality_actual,
    generatedAxisGlobalRationalTriality_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
