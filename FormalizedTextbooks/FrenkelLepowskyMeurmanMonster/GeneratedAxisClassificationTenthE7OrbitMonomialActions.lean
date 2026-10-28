/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitMonomialData

/-! Whole genuine spatial action of the original monomial root-orbit generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- A product of genuine original Golay sign and permutation isometries. -/
def generatedTenthE7OrbitMonoSpatial : leechIsomSubgroup :=
  golaySignIsometry generatedTenthE7OrbitMonoCode *
    golayPermutationIsometry generatedTenthE7OrbitMonoAutomorphism

private theorem sign_cast (i : Fin 24) :
    qSign (generatedTenthE7OrbitMonoCode.val i) =
      ((if generatedTenthE7OrbitMonoCode.val i = 0 then 1 else -1 : ℤ) : ℝ) := by
  by_cases hi : generatedTenthE7OrbitMonoCode.val i = 0 <;> simp [qSign, hi]

/-- The complete actual spatial action is exactly the signed physical matrix. -/
theorem generatedTenth_e7_orbit_mono_apply (x : Fin 24 → ℝ) :
    generatedTenthE7OrbitMonoSpatial.val x =
      generatedTenthE7OrbitMonoMatrix.map (Int.castRingHom ℝ) *ᵥ x := by
  ext i
  change qSign (generatedTenthE7OrbitMonoCode.val i) *
    x (generatedTenthE7OrbitMonoInverse i) = _
  rw [sign_cast]
  simp [generatedTenthE7OrbitMonoMatrix, Matrix.mulVec, dotProduct]

/-- The whole source norm-twelve vector is fixed positively by the genuine generator. -/
theorem generatedTenth_e7_orbit_mono_line :
    generatedTenthE7OrbitMonoSpatial.val (leechCoordinateEmbedding generatedTenthE7XiLine) =
      leechCoordinateEmbedding generatedTenthE7XiLine := by
  rw [generatedTenth_e7_orbit_mono_apply, ← leechCoordinateEmbedding_mulVec,
    generatedTenth_e7_orbit_mono_vectors.1]

/-- The whole perpendicular norm-four source vector is also fixed positively. -/
theorem generatedTenth_e7_orbit_mono_normal :
    generatedTenthE7OrbitMonoSpatial.val (leechCoordinateEmbedding generatedTenthE7XiNormal) =
      leechCoordinateEmbedding generatedTenthE7XiNormal := by
  rw [generatedTenth_e7_orbit_mono_apply, ← leechCoordinateEmbedding_mulVec,
    generatedTenth_e7_orbit_mono_vectors.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
