/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual lattice and binary actions of the p43549632 Singer permutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinBinaryAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The physical permutation matrix acts by the inverse coordinate array. -/
def monsterNortonSingerPhysicalMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if monsterNortonSingerPermInverse 0 i = j then 1 else 0

/-- The checked action on the actual integral lattice basis. -/
def monsterNortonSingerIntegralMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
![
  ![-1, 2, -1, -1, -1, -1, -1, 1, 0, -1, -1, 0, -1, 2, 0, 0, 3, -12, 2, 2, 2, 3, 3, -1],
  ![0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 2, -1, -1, -1, -1, -1, 0],
  ![0, -1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, -1, -1, -1, 0],
  ![0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1, 2, 0, 0, -1, -1, -1, 0],
  ![2, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 2, 0, -1, -1, -1, -1, 1],
  ![0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, -1, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 3, 0, 0, 0, -1, -1, 0],
  ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0, 0, -1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, -1, 0, -1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 2, -1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1, 1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1]
]

set_option maxHeartbeats 8000000 in
-- Check all entries of the two integer basis products.
/-- The integral matrix is certified against the displayed Leech basis. -/
theorem monsterNortonSingerIntegral_certificate :
    monsterNortonSingerPhysicalMatrix * leechBasisMatrix =
      leechBasisMatrix * monsterNortonSingerIntegralMatrix := by
  decide +kernel

/-- The physical matrix is the action of the genuine lattice isometry. -/
theorem monsterNortonSingerPermutation_embedding (u : Fin 24 → ℤ) :
    (monsterNortonSingerPermutationIsometry 0).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (monsterNortonSingerPhysicalMatrix *ᵥ u) := by
  ext i
  simp [monsterNortonSingerPermutationIsometry, golayPermutationIsometry,
    golayRealPermute_apply, leechCoordinateEmbedding, monsterNortonSingerPhysicalMatrix,
    Matrix.mulVec, dotProduct, monsterNortonSingerGolayPermutation,
    monsterNortonSingerPermutation]

/-- The genuine lattice action has the checked integral basis matrix. -/
theorem monsterNortonSingerPermutation_basis (u : Fin 24 → ℤ) :
    (monsterNortonSingerPermutationIsometry 0).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ
        (monsterNortonSingerIntegralMatrix *ᵥ u)) := by
  rw [monsterNortonSingerPermutation_embedding, Matrix.mulVec_mulVec,
    monsterNortonSingerIntegral_certificate, ← Matrix.mulVec_mulVec]

/-- The binary matrix obtained from the actual spin relabeling of Q. -/
def monsterNortonSingerBinaryMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => toAdd (monsterMonomialPermutationImage (monsterNortonSingerCode 0)
    (xiSpinBinaryBasisLift j)).base i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Evaluate the actual spin images and the two binary change-of-basis products.
/-- The spin columns equal the reduction of the actual integral lattice action. -/
theorem monsterNortonSingerBinary_certificate :
    monsterNortonSingerBinaryMatrix = leechHyperbolicInverse *
      monsterNortonSingerIntegralMatrix.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix := by
  decide +kernel

/-- The checked binary matrix is the actual action on the Leech quotient. -/
theorem monsterNortonSingerPermutation_binary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (monsterNortonSingerPermutationIsometry 0) v =
      monsterNortonSingerBinaryMatrix *ᵥ v := by
  rw [leechBinaryAction_of_basis_certificate _ _ monsterNortonSingerPermutation_basis,
    ← monsterNortonSingerBinary_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
