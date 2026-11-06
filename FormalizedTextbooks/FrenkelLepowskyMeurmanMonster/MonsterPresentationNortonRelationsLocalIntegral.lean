/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual integral lattice action of the full source Norton u word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonLocalWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Leech

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual integral inverses for the source physical permutations, with separate spin phases. -/
def monsterNortonPermutationInverseIntegral : Fin 2 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![![![5, 6, 6, 2, 2, 5, 2, 5, 2, 2, 5, 5,
        2, 5, 3, 3, 2, 3, 4, 3, 2, 5, 5, 2],
      ![-2, -2, -1, 0, -1, -2, -1, -1, -1, -1, -2, -1,
        -1, -2, -1, -1, -1, -1, -1, 0, 0, -1, -2, -1],
      ![0, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1,
        0, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0],
      ![0, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1,
        0, -1, -1, -1, 1, 0, -1, -1, 0, 0, -1, 0],
      ![-2, -2, -2, -1, -1, -2, -1, -2, -1, -1, -1, -1,
        -1, -2, -1, -1, -1, -1, -1, -1, -1, -2, -1, -1],
      ![-2, -2, -1, -1, 0, -2, -1, -1, -1, -1, -1, -1,
        -1, -1, 0, -1, -1, -1, -1, 0, 0, -1, -1, -1],
      ![0, -1, -1, 0, 0, -1, 1, -1, 0, 0, 0, -1,
        0, -1, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0],
      ![0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0,
        0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0],
      ![-2, -1, -1, -1, -1, -1, -1, 0, -1, -1, -2, -1,
        -1, -1, -1, -1, -1, 0, -1, -1, 0, -1, -1, -1],
      ![-2, -1, -2, -1, -1, -1, -1, -1, 0, -1, -2, -1,
        -1, 0, -1, -1, -1, 0, -1, -1, 0, -1, -1, -1],
      ![0, -1, -1, 0, 0, 0, 0, -1, 0, 1, -1, -1,
        0, 0, -1, 0, 0, 0, -1, -1, -1, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1,
        0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0],
      ![-2, -2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        0, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0, -1],
      ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1,
        2, 1, 1, 1, 2, 0, 1, 0, 0, 1, 0, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1,
        0, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1,
        0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
        0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 4, 2, 2, 2, 0, 2, -14, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
        0, 0, 0, 0, -1, 0, 0, -1, 0, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 3, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 2, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, -1, -1, -1, -1, 0, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 2, 1, 1, 1, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]]]

set_option maxHeartbeats 20000000 in
-- Verify both 24 by 24 inverse products against the actual certified permutation matrices.
/-- The displayed integral matrices are exact right inverses of the genuine basis actions. -/
theorem monsterNortonPermutationInverseIntegral_certificate : ∀ k : Fin 2,
    omegaOrbitIntegralMatrices (Fin.natAdd 2 k) *
      monsterNortonPermutationInverseIntegral k = 1 := by
  decide +kernel

private theorem basis_inverse (e : leechIsomSubgroup)
    (C D : Matrix (Fin 24) (Fin 24) ℤ)
    (he : ∀ z : Fin 24 → ℤ,
      e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (C *ᵥ z)))
    (hCD : C * D = 1) (z : Fin 24 → ℤ) :
    (e⁻¹).val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (D *ᵥ z)) := by
  apply e.val.injective
  change e.val (e.val.symm (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))) = _
  rw [LinearEquiv.apply_symm_apply, he]
  simp only [Matrix.mulVec_mulVec, hCD, mul_one]

/-- The inverse source permutation has the exact inverse integral basis action. -/
theorem monsterNortonPermutationInverseIntegral_basis (k : Fin 2) (z : Fin 24 → ℤ) :
    ((omegaOrbitPermutationIsometry k)⁻¹).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ
          (monsterNortonPermutationInverseIntegral k *ᵥ z)) := by
  refine basis_inverse (omegaOrbitPermutationIsometry k)
    (omegaOrbitIntegralMatrices (Fin.natAdd 2 k))
    (monsterNortonPermutationInverseIntegral k) ?_
    (monsterNortonPermutationInverseIntegral_certificate k) z
  intro t
  have h := omegaOrbitMonomial_basis (Fin.natAdd 2 k) t
  fin_cases k <;> exact h

/-- The actual full Norton word's integer matrix in the genuine Leech basis. -/
def monsterNortonUIntegralAction : Matrix (Fin 24) (Fin 24) ℤ :=
  monsterSourceY82Integral * monsterNortonPermutationInverseIntegral 0 * co1XiBasisMatrix *
    monsterNortonPermutationInverseIntegral 1 * co1XiBasisMatrix

/-- Every lattice vector is transported by this exact actual Norton integral matrix. -/
theorem monsterNortonUIntegralAction_basis (z : Fin 24 → ℤ) :
    monsterNortonUFiber.val.2.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterNortonUIntegralAction *ᵥ z)) := by
  rw [monsterNortonUFiber_leech]
  change monsterSourceY82Isometry.val (((omegaOrbitPermutationIsometry 0)⁻¹).val
    (co1XiIsometry.val (((omegaOrbitPermutationIsometry 1)⁻¹).val
      (co1XiIsometry.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))))) = _
  have hXi (t : Fin 24 → ℤ) : co1XiIsometry.val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ t)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (co1XiBasisMatrix *ᵥ t)) :=
    co1Xi_embedding_basis t
  rw [hXi, monsterNortonPermutationInverseIntegral_basis,
    hXi, monsterNortonPermutationInverseIntegral_basis,
    monsterSourceY82_embedding_basis]
  simp only [monsterNortonUIntegralAction, Matrix.mulVec_mulVec, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
