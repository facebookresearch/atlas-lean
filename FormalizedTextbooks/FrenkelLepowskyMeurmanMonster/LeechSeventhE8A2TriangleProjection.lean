/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2TriangleData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhScaledProjection

/-! The actual seventh matrix projection has precisely the genuine physical
triangle plane as its image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The three oriented integer coordinate differences on the actual seventh triangle. -/
def leechSeventhTriangleDifference (j : Fin 3) (i : Fin 24) : ℤ :=
  if i = (![16, 16, 17] : Fin 3 → Fin 24) j then 1
  else if i = (![17, 19, 19] : Fin 3 → Fin 24) j then -1 else 0

/-- The original triangle root coordinates are exactly four times these integer differences. -/
theorem leechSeventhTriangleDifference_integral (j : Fin 3) (i : Fin 24) :
    (leechSeventhE8Root (leechSeventhE8A2Indices 537 j)).val i =
      4 * leechSeventhTriangleDifference j i := by
  rw [leechSeventhE8Root_physical, leechSeventhE8A2_triangle_local]
  fin_cases j <;> fin_cases i
  all_goals norm_num [generatedFifthFrameInsert, leechSeventhTriangleDifference]

/-- The original normalized physical triangle roots have the genuine Leech scale. -/
theorem leechSeventhTriangleDifference_real (j : Fin 3) (i : Fin 24) :
    leechSeventhE8A2PlaneRoots 537 j i =
      (4 / Real.sqrt 8 : ℝ) * (leechSeventhTriangleDifference j i : ℝ) := by
  change ((leechSeventhE8Root (leechSeventhE8A2Indices 537 j)).val i : ℝ) / Real.sqrt 8 = _
  rw [leechSeventhTriangleDifference_integral, Int.cast_mul, Int.cast_ofNat]
  ring

/-- The integer difference outer sum is exactly the original triangle projection numerator. -/
theorem leechSeventhTriangleDifference_outer (i k : Fin 24) :
    (∑ j : Fin 3, leechSeventhTriangleDifference j i * leechSeventhTriangleDifference j k) =
      generatedSeventhPlaneNumerator i k := by
  have h : ∀ i k : Fin 24,
      (∑ j : Fin 3, leechSeventhTriangleDifference j i * leechSeventhTriangleDifference j k) =
        generatedSeventhPlaneNumerator i k := by decide +kernel
  exact h i k

/-- The three actual physical roots have outer sum twice the original seventh projection. -/
theorem leechSeventhTriangle_outer_matrix :
    (∑ j : Fin 3, Matrix.vecMulVec (leechSeventhE8A2PlaneRoots 537 j)
      (leechSeventhE8A2PlaneRoots 537 j)) = (2 : ℝ) • generatedSeventhPlaneSupport := by
  have hs : (4 / Real.sqrt 8 : ℝ) ^ 2 = 2 := by
    have h8 : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h8]
    norm_num
  ext i k
  change (∑ j : Fin 3, leechSeventhE8A2PlaneRoots 537 j i *
    leechSeventhE8A2PlaneRoots 537 j k) = 2 * (generatedSeventhPlaneNumerator i k : ℝ)
  simp_rw [leechSeventhTriangleDifference_real]
  have hterm (j : Fin 3) :
      (4 / Real.sqrt 8 : ℝ) * leechSeventhTriangleDifference j i *
        ((4 / Real.sqrt 8 : ℝ) * leechSeventhTriangleDifference j k) =
      2 * ((leechSeventhTriangleDifference j i * leechSeventhTriangleDifference j k : ℤ) : ℝ) := by
    rw [Int.cast_mul, ← hs]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Int.cast_sum, leechSeventhTriangleDifference_outer]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
