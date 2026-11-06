/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMiddleProjector

/-! Executable integer numerators for the actual final fifth-axis short coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times a final pair coordinate, using its actual physical coordinate pair. -/
def generatedFifthFinalPairNumerator (s : Fin 2) (a b : Fin 24) : ℤ :=
  (if s = 0 then 1 else -1) * generatedFifthMiddleProjectorNumerator a b

/-- Sixteen times a final outgoing octad coordinate, with its full preferred-Q sign. -/
def generatedFifthFinalOctadNumerator (j : Fin 56) (e : Fin 64) : ℤ :=
  2 * trialityIntegerMatrix e (generatedFifthEvenRootSign j) *
    (if generatedFifthEvenCoefficientCache j = 0 then 1 else -1)

/-- Every final pair coefficient equals its executable integer numerator divided by sixteen. -/
theorem generatedFifth_final_pair_numerator (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (s, p)) =
      (generatedFifthFinalPairNumerator s
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) / 16 := by
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> decide
  rcases hs with rfl | rfl
  · simpa only [generatedFifthFinalPairNumerator, ite_true, one_mul] using
      generatedFifth_final_pair_minus p
  · simpa only [generatedFifthFinalPairNumerator, show (1 : Fin 2) ≠ 0 by decide,
      ite_false, neg_one_mul, Int.cast_neg] using generatedFifth_final_pair_plus p

/-- Every outgoing octad coefficient equals its executable integer numerator divided by sixteen. -/
theorem generatedFifth_final_octad_numerator (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode generatedFifthAxis).2.1
      (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        (generatedFifthFinalOctadNumerator j e : ℝ) / 16 := by
  rw [generatedFifth_final_octad_coordinate, generatedFifth_even_coefficient_cache]
  simp only [trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, generatedFifthFinalOctadNumerator, Int.cast_mul, Int.cast_ofNat,
    Int.cast_ite, Int.cast_one, Int.cast_neg, qSign]
  change (1 / 8 : ℝ) * (trialityIntegerMatrix e (generatedFifthEvenRootSign j) : ℝ) *
      (if generatedFifthEvenCoefficientCache j = 0 then 1 else -1) =
    (2 * (trialityIntegerMatrix e (generatedFifthEvenRootSign j) : ℝ) *
      (if generatedFifthEvenCoefficientCache j = 0 then 1 else -1)) / 16
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
