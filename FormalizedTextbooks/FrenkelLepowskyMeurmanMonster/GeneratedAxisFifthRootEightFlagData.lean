/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Original integral vectors for the two distinguished lines at fifth root 8. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Primitive physical direction of the higher distinguished matrix eigenspace. -/
def generatedFifthRootEightHighDirection : Fin 24 → ℤ :=
  ![0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0]

/-- Primitive physical direction of the lower distinguished matrix eigenspace. -/
def generatedFifthRootEightLowDirection : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]

/-- The actual norm 4 integral vector on the lower line. -/
def generatedFifthRootEightNormFourVector (i : Fin 24) : ℤ :=
  4 * generatedFifthRootEightLowDirection i

/-- The actual norm 6 integral vector joining the two distinguished lines. -/
def generatedFifthRootEightNormSixVector (i : Fin 24) : ℤ :=
  2 * (generatedFifthRootEightHighDirection i + generatedFifthRootEightLowDirection i)

/-- Membership is checked in the original Golay congruence lattice. -/
theorem generatedFifthRootEight_norm_four_mem :
    generatedFifthRootEightNormFourVector ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    simp only [generatedFifthRootEightNormFourVector, Int.cast_mul, Int.cast_ofNat,
      Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, Int.cast_zero, add_zero,
      show (4 : ZMod 4) = 0 by decide, zero_mul]
  · have hs : ∑ i, generatedFifthRootEightNormFourVector i = 8 := by decide +kernel
    rw [hs]
    decide

/-- The joining vector uses the original Golay codeword with literal label 825. -/
theorem generatedFifthRootEight_norm_six_mem :
    generatedFifthRootEightNormSixVector ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, golayEncoder (golayLabelCoefficients 825), ⟨_, rfl⟩, ?_, ?_⟩
  · intro i
    revert i
    decide +kernel
  · have hs : ∑ i, generatedFifthRootEightNormSixVector i = 8 := by decide +kernel
    rw [hs]
    decide

/-- Every physical square and pairing keeps the original normalization by 8. -/
theorem generatedFifthRootEight_flag_integer_norms :
    leechSquareSum generatedFifthRootEightNormFourVector = 32 ∧
    leechSquareSum generatedFifthRootEightNormSixVector = 48 ∧
    (∑ i, generatedFifthRootEightNormFourVector i *
      generatedFifthRootEightNormSixVector i) = 16 := by
  decide +kernel

/-- The distinguished actual norm 4 Leech lattice element. -/
def generatedFifthRootEightNormFour : leechIntegral :=
  ⟨generatedFifthRootEightNormFourVector, generatedFifthRootEight_norm_four_mem⟩

/-- The distinguished actual norm 6 Leech lattice element. -/
def generatedFifthRootEightNormSix : leechIntegral :=
  ⟨generatedFifthRootEightNormSixVector, generatedFifthRootEight_norm_six_mem⟩

/-- Twice the norm 6 vector minus the norm 4 vector lies on the higher distinguished line. -/
def generatedFifthRootEightNormTwenty : leechIntegral :=
  (2 : ℕ) • generatedFifthRootEightNormSix - generatedFifthRootEightNormFour

/-- Its original physical coordinates are four times the primitive higher direction. -/
theorem generatedFifthRootEight_norm_twenty_coordinates (i : Fin 24) :
    generatedFifthRootEightNormTwenty.val i = 4 * generatedFifthRootEightHighDirection i := by
  change 2 * generatedFifthRootEightNormSixVector i -
    generatedFifthRootEightNormFourVector i = _
  unfold generatedFifthRootEightNormSixVector generatedFifthRootEightNormFourVector
  ring

/-- The actual joining flag gives a norm 20 vector on the higher matrix line. -/
theorem generatedFifthRootEight_norm_twenty_square_sum :
    leechSquareSum generatedFifthRootEightNormTwenty.val = 160 := by
  have h : generatedFifthRootEightNormTwenty.val =
      fun i => 4 * generatedFifthRootEightHighDirection i :=
    funext generatedFifthRootEight_norm_twenty_coordinates
  rw [h]
  decide +kernel

/-- The integer matrix of ten times the higher-line orthogonal projection. -/
def generatedFifthRootEightHighProjectionInteger : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j =>
    generatedFifthRootEightHighDirection i * generatedFifthRootEightHighDirection j

/-- The integer matrix of twice the lower-line orthogonal projection. -/
def generatedFifthRootEightLowProjectionInteger : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => generatedFifthRootEightLowDirection i * generatedFifthRootEightLowDirection j

set_option maxHeartbeats 64000000 in
-- Verify both complete rank-one projections and their mutual orthogonality.
/-- The two physical integer matrices are orthogonal multiples of projections. -/
theorem generatedFifthRootEight_integer_flag_projections :
    generatedFifthRootEightHighProjectionInteger * generatedFifthRootEightHighProjectionInteger =
        (10 : ℕ) • generatedFifthRootEightHighProjectionInteger ∧
    generatedFifthRootEightLowProjectionInteger * generatedFifthRootEightLowProjectionInteger =
        (2 : ℕ) • generatedFifthRootEightLowProjectionInteger ∧
    generatedFifthRootEightHighProjectionInteger * generatedFifthRootEightLowProjectionInteger = 0 ∧
    generatedFifthRootEightLowProjectionInteger * generatedFifthRootEightHighProjectionInteger = 0
      := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
