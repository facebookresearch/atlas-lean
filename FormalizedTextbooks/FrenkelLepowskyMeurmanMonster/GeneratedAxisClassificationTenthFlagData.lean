/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFlagMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration

/-! Concrete genuine integral data of the seven pair lines and orthogonal norm 12 line. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Signed physical direction of the six-coordinate distinguished line. -/
def generatedTenthLineDirection : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1]

/-- Original integral norm 12 vector on the distinguished physical line. -/
def generatedTenthNormTwelveVector (i : Fin 24) : ℤ := 4 * generatedTenthLineDirection i

/-- The actual signed vector belongs to the original integral Leech lattice. -/
theorem generatedTenth_norm_twelve_vector_mem : generatedTenthNormTwelveVector ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    simp only [generatedTenthNormTwelveVector, Int.cast_mul, Int.cast_ofNat,
      Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, Int.cast_zero, add_zero,
      show (4 : ZMod 4) = 0 by decide, zero_mul]
  · have hs : ∑ i, generatedTenthNormTwelveVector i = 8 := by decide +kernel
    rw [hs]
    change (8 : ZMod 8) = 0
    decide

/-- The original physical square-sum is 96, hence normalized Leech norm 12. -/
theorem generatedTenth_norm_twelve_square_sum :
    leechSquareSum generatedTenthNormTwelveVector = 96 := by decide +kernel

/-- The intrinsic original Leech lattice vector on the distinguished line. -/
def generatedTenthNormTwelveLine : leechIntegral :=
  ⟨generatedTenthNormTwelveVector, generatedTenth_norm_twelve_vector_mem⟩

/-- The seven actual disjoint pairs; identifier 7 denotes the remaining ten coordinates. -/
def generatedTenthPairLineIdentifier : Fin 24 → ℕ :=
  ![0, 7, 7, 0, 7, 1, 1, 7, 7, 2, 2, 7, 3, 7, 7, 3, 7, 4, 5, 6, 5, 7, 6, 4]

/-- Twice the projection onto the seven actual mutually orthogonal pair lines. -/
def generatedTenthPairProjectionInteger : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if generatedTenthPairLineIdentifier i < 7 ∧
      generatedTenthPairLineIdentifier i = generatedTenthPairLineIdentifier j then 1 else 0

/-- Six times the projection onto the actual distinguished line. -/
def generatedTenthLineProjectionInteger : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  generatedTenthLineDirection i * generatedTenthLineDirection j

set_option maxHeartbeats 64000000 in
-- Check the complete integer projector identities in original physical coordinates.
/-- The two original integer matrices are mutually orthogonal multiples of projections. -/
theorem generatedTenth_integer_flag_projections :
    generatedTenthPairProjectionInteger * generatedTenthPairProjectionInteger =
        (2 : ℕ) • generatedTenthPairProjectionInteger ∧
    generatedTenthLineProjectionInteger * generatedTenthLineProjectionInteger =
        (6 : ℕ) • generatedTenthLineProjectionInteger ∧
    generatedTenthPairProjectionInteger * generatedTenthLineProjectionInteger = 0 ∧
    generatedTenthLineProjectionInteger * generatedTenthPairProjectionInteger = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
