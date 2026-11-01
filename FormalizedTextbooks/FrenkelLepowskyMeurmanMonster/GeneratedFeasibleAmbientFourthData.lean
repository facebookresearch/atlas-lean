/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIntegerZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOdd
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairPhaseCache

/-! Integer data for the actual Fourth prototype.

The matrix numerator over 16 is the projector diagonal with the single flag entry on the
coordinates eight and eleven; it dominates `2 I`. All short numerators are written over
16 with the certified fast pair and octad catalogues. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The matrix numerator, over 16, of the actual Fourth prototype. -/
def generatedFeasibleAmbientFourthN (i j : Fin 24) : ℤ :=
  if i = j then generatedFourthProjectionDiagonal i
  else if (i = 8 ∧ j = 11) ∨ (i = 11 ∧ j = 8) then -8 else 0

/-- Rank-one directions of the positive semidefinite certificate. -/
def generatedFeasibleAmbientFourthW (k i : Fin 24) : ℤ :=
  if k = 8 then (if i = 8 then 1 else if i = 11 then -1 else 0)
  else if i = k then 1 else 0

/-- Nonnegative weights of the positive semidefinite certificate. -/
def generatedFeasibleAmbientFourthC (k : Fin 24) : ℤ :=
  if k = 8 then 8 else if 4 ≤ k.val ∧ k.val < 12 then 0 else 4

private theorem decomp : ∀ i j : Fin 24, 1 * generatedFeasibleAmbientFourthN i j =
    1 * 2 * (if i = j then 1 else 0) + ∑ k, generatedFeasibleAmbientFourthC k *
      (generatedFeasibleAmbientFourthW k i * generatedFeasibleAmbientFourthW k j) := by
  unfold generatedFeasibleAmbientFourthN generatedFeasibleAmbientFourthC
    generatedFeasibleAmbientFourthW generatedFourthProjectionDiagonal
  decide +kernel

/-- The Fourth matrix numerator dominates `2 I` on every integral vector. -/
theorem generatedFeasibleAmbient_fourth_quad_ge (u : Fin 24 → ℤ) :
    2 * ∑ i, u i ^ 2 ≤ generatedFeasibleAmbientQuad generatedFeasibleAmbientFourthN u :=
  generatedFeasibleAmbient_quad_ge_of_decomp _ 2 1 generatedFeasibleAmbientFourthC
    generatedFeasibleAmbientFourthW (by norm_num)
    (by intro k; unfold generatedFeasibleAmbientFourthC; split_ifs <;> norm_num) decomp u

private theorem pairIndex_coordinates (i j : Fin 24) (h : i ≠ j) :
    griessCoordinatePair (griessPairIndex i j h) = if i < j then (i, j) else (j, i) := by
  simp only [griessCoordinatePair, griessPairIndex, Equiv.apply_symm_apply]

private theorem offdiag_check : ∀ i j : Fin 24, i ≠ j →
    (if (if i < j then (i, j) else (j, i)) = ((8 : Fin 24), (11 : Fin 24)) then (-8 : ℤ)
      else 0) = generatedFeasibleAmbientFourthN i j := by
  unfold generatedFeasibleAmbientFourthN
  decide +kernel

/-- Every actual matrix coordinate of the Fourth prototype. -/
theorem generatedFeasibleAmbient_fourth_matrix (i j : Fin 24) :
    (griessConwayEncode generatedFourthAxis).1 i j =
      (generatedFeasibleAmbientFourthN i j : ℝ) / 16 := by
  by_cases h : i = j
  · subst h
    rw [generatedFourth_matrix_diagonal]
    simp [generatedFeasibleAmbientFourthN]
  · rw [generatedFourth_matrix_off_diagonal i j h, pairIndex_coordinates,
      generatedFourth_pair_phase_zero, qSign_zero, ← offdiag_check i j h]
    split_ifs <;> norm_num

/-- The short numerators, over 16, of the actual Fourth prototype. -/
def generatedFeasibleAmbientFourthShort : GriessShortIndex → ℤ
  | Sum.inl (s, p) => generatedFourthLiftShortPairNumerator s
      (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2
  | Sum.inr (Sum.inl (o, e)) =>
      2 * generatedFourthQShortBasisOctadNumerator (generatedAxisGlobalOctadCodeData o) e
  | Sum.inr (Sum.inr _) => 0

/-- Every actual short coordinate of the Fourth prototype. -/
theorem generatedFeasibleAmbient_fourth_short (r : GriessShortIndex) :
    (griessConwayEncode generatedFourthAxis).2.1 r =
      (generatedFeasibleAmbientFourthShort r : ℝ) / 16 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · rw [generatedFourth_lift_short_pair_numerator]
    simp only [generatedFeasibleAmbientFourthShort, generatedAxisGlobalPairCoordinates_actual]
  · rw [generatedFourthQShortBasis_octad_coordinate]
    simp only [generatedFeasibleAmbientFourthShort, generatedAxisGlobalOctadCodeData_actual]
    push_cast
    ring
  · rw [generatedFourthQShortBasis_odd_zero]
    simp [generatedFeasibleAmbientFourthShort]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
