/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIntegerZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairMarkings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowComplete

/-! The Ninth local family: no actual signed-short axis is orthogonal to the actual Ninth
prototype.

Every short coordinate of the prototype has absolute value at most one eighth, by the
existing marking theorems, while its matrix numerator dominates `8 I` over 32. Hence the
matrix contraction against every actual short vector is at least one, and the pairing
`2 q - 8 (±1) S` never vanishes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Rank-one directions of the positive semidefinite certificate: the 24 coordinate lines and
the eight coupled coordinate pairs. -/
def generatedFeasibleAmbientNinthW (k : Fin 32) (i : Fin 24) : ℤ :=
  if h : k.val < 24 then (if i.val = k.val then 1 else 0)
  else
    let pairs : Fin 8 → ℕ × ℕ × ℤ :=
      ![(0, 23, 1), (6, 17, 1), (10, 13, 1), (14, 15, 1), (1, 16, -1), (2, 4, -1),
        (7, 22, -1), (19, 21, -1)]
    let t := pairs ⟨k.val - 24, by omega⟩
    if i.val = t.1 then 1 else if i.val = t.2.1 then t.2.2 else 0

/-- Nonnegative weights of the positive semidefinite certificate. -/
def generatedFeasibleAmbientNinthC (k : Fin 32) : ℤ :=
  if h : k.val < 24 then
    generatedNinthDiagonalNumerator ⟨k.val, h⟩ - 8 -
      (if k.val ∈ ([0, 23, 6, 17, 10, 13, 14, 15, 1, 16, 2, 4, 7, 22, 19, 21] : List ℕ)
        then 2 else 0)
  else 2

set_option maxRecDepth 100000 in
-- The 576 matrix entries are checked against 32 rank-one terms.
private theorem decomp : ∀ i j : Fin 24, 1 * generatedNinthMatrixNumerator i j =
    1 * 8 * (if i = j then 1 else 0) + ∑ k, generatedFeasibleAmbientNinthC k *
      (generatedFeasibleAmbientNinthW k i * generatedFeasibleAmbientNinthW k j) := by
  unfold generatedNinthMatrixNumerator generatedFeasibleAmbientNinthC generatedFeasibleAmbientNinthW
  decide +kernel

private theorem weights_nonneg : ∀ k : Fin 32, 0 ≤ generatedFeasibleAmbientNinthC k := by
  unfold generatedFeasibleAmbientNinthC
  decide +kernel

private theorem quad_ge (r : GriessShortIndex) :
    256 ≤ generatedFeasibleAmbientQuad generatedNinthMatrixNumerator (griessShortIntegral r) := by
  have h := generatedFeasibleAmbient_quad_ge_of_decomp _ 8 1 generatedFeasibleAmbientNinthC
    generatedFeasibleAmbientNinthW (by norm_num) weights_nonneg decomp (griessShortIntegral r)
  have hs := griessShortIntegral_squareSum r
  unfold leechSquareSum at hs
  rw [hs] at h
  linarith

/-- The matrix contraction against every actual short vector is at least one. -/
private theorem contraction_ge (r : GriessShortIndex) :
    1 ≤ axisMatrixContraction (griessShortVector r) (griessConwayEncode generatedNinthAxis).1 := by
  have hc : axisMatrixContraction (griessShortVector r) (griessConwayEncode generatedNinthAxis).1 =
      (generatedFeasibleAmbientQuad generatedNinthMatrixNumerator (griessShortIntegral r) : ℝ) /
        256 := by
    rw [generatedNinth_axis_matrix]
    unfold axisMatrixContraction generatedFeasibleAmbientQuad generatedNinthAxisMatrix
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    calc griessShortVector r i * ((generatedNinthMatrixNumerator i j : ℝ) / 32) *
          griessShortVector r j
        = (generatedNinthMatrixNumerator i j : ℝ) / 32 *
          (griessShortVector r i * griessShortVector r j) := by ring
      _ = (generatedNinthMatrixNumerator i j : ℝ) / 32 *
          ((griessShortIntegral r i : ℝ) * griessShortIntegral r j / 8) := by
          rw [generatedFeasibleAmbient_shortVector_mul]
      _ = _ := by ring
  rw [hc, le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
  have h := quad_ge r
  have h' : ((256 : ℤ) : ℝ) ≤
      (generatedFeasibleAmbientQuad generatedNinthMatrixNumerator (griessShortIntegral r) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- Every actual short coordinate of the Ninth prototype has absolute value at most 1/8. -/
private theorem short_abs_le (r : GriessShortIndex) :
    |(griessConwayEncode generatedNinthAxis).2.1 r| ≤ 1 / 8 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · by_cases h : (s, p) ∈ generatedNinthFinalPairMarkings
    · rw [generatedNinth_final_pair_marking_coefficient s p h]
      norm_num
    · exact (generatedNinth_final_pair_nonmarking_bound s p h).trans (by norm_num)
  · by_cases h : o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns
    · rw [generatedNinth_final_octad_marking_coefficient_of_certificates
        generatedNinth_short_row_certificate_all o e h]
      norm_num
    · exact (generatedNinth_final_octad_nonmarking_bound_of_certificates
        generatedNinth_short_row_certificate_all o e h).trans (by norm_num)
  · by_cases h : (d, i) ∈ generatedNinthOddMarkings
    · rw [generatedNinth_final_odd_marking_coefficient d i h]
    · exact (generatedNinth_final_odd_nonmarking_bound d i h).trans (by norm_num)

/-- No actual signed-short axis is orthogonal to the actual Ninth prototype. -/
theorem generatedFeasibleAmbient_ninth_form_ne (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedNinthAxis ≠ 0 := by
  rw [generatedFeasibleAmbient_axis_form]
  have hq := contraction_ge r
  have hs := abs_le.mp (short_abs_le r)
  have hc : qSign c = 1 ∨ qSign c = -1 := by
    unfold qSign
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with hc | hc <;> rw [hc] <;> intro h <;> linarith [hs.1, hs.2]

/-- No actual signed-short axis is orthogonal to the actual Ninth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_ninth :
    generatedFeasibleAmbientAxisZeroCount generatedNinthAxis = 0 := by
  unfold generatedFeasibleAmbientAxisZeroCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨⟨r, c⟩, h⟩
  exact generatedFeasibleAmbient_ninth_form_ne r c h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
