/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliMiddleNumeric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOctadTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOddTriality

/-! All preferred short families retain their exact original triality source formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The pair source formula uses the already checked original preferred pair enumeration. -/
def generatedNinthLowerPairSourceInteger (s : Fin 2) (p : Fin 276) : ℤ :=
  let i := (generatedNinthCoordinatePairData p).1
  let j := (generatedNinthCoordinatePairData p).2
  8 * (generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 0 i j) -
      generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 1 i j)) +
    (if s = 0 then generatedNinthMiddleMatrixInteger i j
      else -generatedNinthMiddleMatrixInteger i j)

/-- The complete256-normalized preferred short numerator from the original spatial source. -/
def generatedNinthLowerShortSourceInteger : GriessShortIndex → ℤ
  | Sum.inl (s, p) => generatedNinthLowerPairSourceInteger s p
  | Sum.inr (Sum.inl (o, e)) =>
      2 * ∑ f : Fin 64, trialityIntegerMatrix e f *
        generatedNinthLowerMiddleShortCoefficient (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, i)) =>
      4 * nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedNinthMiddleNumerator ⟨d.val, by omega⟩ i +
          generatedNinthMiddleNumerator ⟨d.val + 2048, by omega⟩ i)

/-- All original rows bind every actual preferred short coordinate to its full source numerator. -/
theorem generatedNinth_lower_short_source_generic_actual
    (hcache : ∀ r : GriessShortIndex,
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
        generatedFifthAxis)).2.1 r =
          (generatedNinthLowerMiddleShortCoefficient r : ℝ) / 16)
    (r : GriessShortIndex) :
    256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerShortSourceInteger r : ℝ) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rw [generatedNinth_final_pair_integer]
    simp only [generatedNinthLowerShortSourceInteger, generatedNinthLowerPairSourceInteger,
      generatedNinthFinalPairInteger, generatedNinth_coordinate_pair_actual]
    ring
  · rw [generatedNinthAxis_local_expression,
      generatedNinth_final_triality_octad_integer _ o
        (fun f => generatedNinthLowerMiddleShortCoefficient (Sum.inr (Sum.inl (o, f))))
        (fun f => hcache _) e]
    simp only [generatedNinthLowerShortSourceInteger, Int.cast_mul, Int.cast_ofNat]
    ring
  · rw [generatedNinthAxis_local_expression, generatedNinth_final_triality_odd_coordinate,
      generatedNinth_middle_numeric, generatedNinth_middle_numeric]
    simp only [generatedNinthLowerShortSourceInteger, nortonUIntegerLabel_coeff,
      Int.cast_mul, Int.cast_ofNat, Int.cast_add, nortonUIntegerSign_real]
    have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs]
    rw [hsq]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
