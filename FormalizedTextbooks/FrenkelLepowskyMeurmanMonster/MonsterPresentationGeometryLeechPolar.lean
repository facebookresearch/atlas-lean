/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual binary polar form is the integral Leech inner product divided by eight. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryPolarDuality

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual lattice inner product is eight times the supplied integral basis Gram form. -/
theorem monsterGeometryLeech_dot (u v : leechIntegral) :
    dotProduct u.val v.val =
      8 * leechBasisGram.toBilin' (leechExplicitCoordinates u) (leechExplicitCoordinates v) := by
  rw [← leechExplicitCoordinates_vector u, ← leechExplicitCoordinates_vector v]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec leechBasisMatrix
    (leechExplicitCoordinates u) (leechBasisMatrix.mulVec (leechExplicitCoordinates v)),
    Matrix.mulVec_mulVec,
    leechBasisMatrix_gram, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.toBilin'_apply']

/-- The integral cross term of half-norm is the actual basis Gram pairing. -/
theorem monsterGeometryLeech_halfNorm_polar (x y : Fin 24 → ℤ) :
    leechIntegralHalfNorm (x + y) - leechIntegralHalfNorm x - leechIntegralHalfNorm y =
      leechBasisGram.toBilin' x y := by
  simp only [leechIntegralHalfNorm, LinearMap.BilinMap.toQuadraticMap_apply,
    map_add, LinearMap.add_apply]
  rw [← leechBasisHalfGram_identity, map_add]
  simp only [LinearMap.add_apply]
  have ht : leechBasisHalfGram.transpose.toBilin' x y =
      leechBasisHalfGram.toBilin' y x := by
    simp only [Matrix.toBilin'_apply']
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [ht]
  ring

/-- Reduction of actual integral half-norm agrees with the source binary coordinates. -/
theorem monsterGeometryLeech_halfNorm (u : leechIntegral) :
    (leechIntegralHalfNorm (leechExplicitCoordinates u) : ZMod 2) =
      squareQuad (leechHyperbolicCoordinates (leechReduction u)) := by
  have h := leechHyperbolicCoordinates_halfNorm u
  rw [← leechExplicitCoordinates_vector u, leechBasis_squareSum,
    Int.mul_ediv_cancel_left _ (by decide)] at h
  exact h

/-- The genuine polar pairing is the physical integral Leech inner product divided by eight. -/
theorem monsterGeometryLeech_polar (u v : leechIntegral) :
    co1BinaryPolar (leechHyperbolicCoordinates (leechReduction u))
        (leechHyperbolicCoordinates (leechReduction v)) =
      ((dotProduct u.val v.val / 8 : ℤ) : ZMod 2) := by
  rw [co1BinaryPolar_quadratic, ← map_add, ← map_add,
    ← monsterGeometryLeech_halfNorm, ← monsterGeometryLeech_halfNorm,
    ← monsterGeometryLeech_halfNorm]
  rw [map_add, ← Int.cast_sub, ← Int.cast_sub,
    monsterGeometryLeech_halfNorm_polar, monsterGeometryLeech_dot,
    Int.mul_ediv_cancel_left _ (by decide)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
