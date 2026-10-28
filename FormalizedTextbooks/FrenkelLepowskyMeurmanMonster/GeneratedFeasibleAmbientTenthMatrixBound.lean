/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIntegerZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthMatrix

/-! The Tenth prototype matrix dominates `17/64 I`: its contraction against every actual short
vector is at least `17/16`, so a short coordinate of absolute value at most `1/4` excludes
orthogonality. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Twice the matrix numerator (over 32) of the Tenth prototype. -/
def generatedFeasibleAmbientTenthN2 (i j : Fin 24) : ℤ := 2 * generatedTenthMatrixNumerator i j

/-- Rank-one directions of the positive semidefinite certificate for `2 N - 17 I`. -/
def generatedFeasibleAmbientTenthPsdW : Fin 24 → Fin 24 → ℤ :=
  ![![5, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 5, 0, 0, 4, 0, 0, 0, 0, 0, 4, -4, 0, 0, -4, 0,
      0, 0, 0, 0, 4], ![0, 0, 0, 0, 0, 5, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
      0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 4, -4, 0, 0, -4, 0, 0, 0, 0, 0, 4], ![0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 4, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, -4, 0, 0, -4, 0, 0, 0, 0, 0, 4], ![0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 4, 0, 0, 0, 0, 0, -4], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 0,
      0, 0, 0, 0, 64], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 4, 0, 0,
      0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 4, 0], ![0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1]]

/-- Nonnegative weights of the positive semidefinite certificate. -/
def generatedFeasibleAmbientTenthPsdC : Fin 24 → ℤ :=
  ![177021, 885105, 885105, 1593189, 177021, 177021, 1593189, 19669, 885105, 177021, 1593189,
      885105, 177021, 7565, 4005, 1593189, 885105, 585, 177021, 177021, 1593189, 885105,
      1593189, 2237625]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- The 576 matrix entries are checked against 24 rank-one terms.
private theorem decomp : ∀ i j : Fin 24, 885105 * generatedFeasibleAmbientTenthN2 i j =
    885105 * 17 * (if i = j then 1 else 0) + ∑ k, generatedFeasibleAmbientTenthPsdC k *
      (generatedFeasibleAmbientTenthPsdW k i * generatedFeasibleAmbientTenthPsdW k j) := by
  unfold generatedFeasibleAmbientTenthN2 generatedTenthMatrixNumerator
      generatedFeasibleAmbientTenthPsdC generatedFeasibleAmbientTenthPsdW
  decide +kernel

private theorem weights_nonneg : ∀ k : Fin 24, 0 ≤ generatedFeasibleAmbientTenthPsdC k := by
  unfold generatedFeasibleAmbientTenthPsdC
  decide +kernel

/-- The contraction of the Tenth matrix against every actual short vector is at least `17/16`. -/
theorem generatedFeasibleAmbientTenth_contraction_ge (r : GriessShortIndex) :
    17 / 16 ≤ axisMatrixContraction (griessShortVector r)
      (griessConwayEncode generatedTenthAxis).1 := by
  have h := generatedFeasibleAmbient_quad_ge_of_decomp _ 17 885105
      generatedFeasibleAmbientTenthPsdC generatedFeasibleAmbientTenthPsdW
    (by norm_num) weights_nonneg decomp (griessShortIntegral r)
  have hs := griessShortIntegral_squareSum r
  unfold leechSquareSum at hs
  rw [hs] at h
  have hq : axisMatrixContraction (griessShortVector r) (griessConwayEncode generatedTenthAxis).1 =
      (generatedFeasibleAmbientQuad generatedFeasibleAmbientTenthN2 (griessShortIntegral r) : ℝ) /
          512 := by
    rw [generatedTenth_matrix_actual]
    unfold axisMatrixContraction generatedFeasibleAmbientQuad generatedFeasibleAmbientTenthN2
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    calc griessShortVector r i * ((generatedTenthMatrixNumerator i j : ℝ) / 32) *
          griessShortVector r j
        = (generatedTenthMatrixNumerator i j : ℝ) / 32 *
          (griessShortVector r i * griessShortVector r j) := by ring
      _ = (generatedTenthMatrixNumerator i j : ℝ) / 32 *
          ((griessShortIntegral r i : ℝ) * griessShortIntegral r j / 8) := by
          rw [generatedFeasibleAmbient_shortVector_mul]
      _ = _ := by ring
  rw [hq, le_div_iff₀ (by norm_num : (0 : ℝ) < 512)]
  have h' : ((17 * 32 : ℤ) : ℝ) ≤
      (generatedFeasibleAmbientQuad generatedFeasibleAmbientTenthN2 (griessShortIntegral r) : ℝ)
          := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- A short coordinate of absolute value at most `1/4` excludes orthogonality to the Tenth
prototype. -/
theorem generatedFeasibleAmbientTenth_form_ne_of_abs (r : GriessShortIndex) (c : ZMod 2)
    (h : |(griessConwayEncode generatedTenthAxis).2.1 r| ≤ 1 / 4) :
    griessForm (conwayShortAxis r c) generatedTenthAxis ≠ 0 := by
  rw [generatedFeasibleAmbient_axis_form]
  have hq := generatedFeasibleAmbientTenth_contraction_ge r
  have hs := abs_le.mp h
  have hc : qSign c = 1 ∨ qSign c = -1 := by
    unfold qSign
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with hc | hc <;> rw [hc] <;> intro he <;> linarith [hs.1, hs.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
