/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7Slice

/-! Complete integral projection equations for the actual E7 root slice. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Four times the E7 projection square equals the octad energy minus its normal component. -/
theorem generatedTenth_e7_projection_square_partition (u : Fin 24 → ℤ) :
    leechSquareSum (generatedTenthE7ProjectionInteger *ᵥ u) +
      4 * generatedTenthE7OutsideSquare u + 2 * (u 16 + u 21) ^ 2 =
        4 * leechSquareSum u := by
  simp [leechSquareSum, generatedTenthE7ProjectionInteger,
    generatedTenthE7NormalDirection, generatedTenthE7OutsideSquare,
    generatedTenthE7OctadSupport, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
  ring

/-- The actual norm-four roots whose E7 projections have physical squared norm three. -/
def generatedTenthE7SliceIntegral : Set (Fin 24 → ℤ) :=
  {u | u ∈ leechIntegral ∧ leechSquareSum u = 32 ∧
    leechSquareSum (generatedTenthE7ProjectionInteger *ᵥ u) = 96}

/-- Every genuine root in the projection-three slice lies in the actual enclosing octad. -/
theorem generatedTenth_e7_slice_supported (u : Fin 24 → ℤ)
    (hu : u ∈ generatedTenthE7SliceIntegral) :
    ∀ i, i ∉ generatedTenthE7OctadSupport → u i = 0 := by
  rcases hu with ⟨hu, hn, hp⟩
  have h := generatedTenth_e7_projection_square_partition u
  rw [hn, hp] at h
  apply generatedTenth_e7_short_supported_of_outside_bound ⟨u, hu⟩ hn
  nlinarith [sq_nonneg (u 16 + u 21)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
