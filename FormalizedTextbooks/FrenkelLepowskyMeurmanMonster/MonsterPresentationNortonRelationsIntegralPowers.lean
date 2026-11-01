/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integral coordinates for positive and inverse Norton actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIntegralAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem basis_power (e : leechIsomSubgroup)
    (C : Matrix (Fin 24) (Fin 24) ℤ)
    (he : ∀ z : Fin 24 → ℤ,
      e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (C *ᵥ z)))
    (n : ℕ) (z : Fin 24 → ℤ) :
    (e ^ n).val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ ((C ^ n) *ᵥ z)) := by
  induction n with
  | zero => simp only [pow_zero, Matrix.one_mulVec]; rfl
  | succ n ih =>
    rw [pow_succ']
    change e.val ((e ^ n).val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))) = _
    rw [ih, he, pow_succ']
    simp only [Matrix.mulVec_mulVec]

/-- All positive Norton powers have the actual integral matrix powers. -/
theorem monsterNortonUIntegralAction_power_basis (n : ℕ) (z : Fin 24 → ℤ) :
    (monsterNortonUFiber ^ n).val.2.val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ ((monsterNortonUIntegralAction ^ n) *ᵥ z)) :=
  basis_power monsterNortonUFiber.val.2 _ monsterNortonUIntegralAction_basis n z

/-- The inverse lattice word keeps the reversed order of its five actual factors. -/
def monsterNortonUInverseIntegralAction : Matrix (Fin 24) (Fin 24) ℤ :=
  co1XiBasisMatrix ^ 2 * omegaOrbitIntegralMatrices 3 * co1XiBasisMatrix ^ 2 *
    omegaOrbitIntegralMatrices 2 * monsterSourceY82Integral

private theorem xi_inverse_basis (z : Fin 24 → ℤ) :
    (co1XiIsometry⁻¹).val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ ((co1XiBasisMatrix ^ 2) *ᵥ z)) := by
  have hc : co1XiIsometry * (co1XiIsometry * co1XiIsometry) = 1 := by
    simpa only [pow_succ, pow_two, pow_one, pow_zero, one_mul, mul_assoc] using co1XiIsometry_cube
  have hi : co1XiIsometry⁻¹ = co1XiIsometry * co1XiIsometry := by
    calc
      _ = co1XiIsometry⁻¹ * (co1XiIsometry * (co1XiIsometry * co1XiIsometry)) := by
        rw [hc, mul_one]
      _ = _ := by group
  rw [hi]
  change co1XiIsometry.val (co1XiIsometry.val
    (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))) = _
  have hx (t : Fin 24 → ℤ) : co1XiIsometry.val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ t)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (co1XiBasisMatrix *ᵥ t)) :=
    co1Xi_embedding_basis t
  rw [hx, hx, pow_two]
  simp only [Matrix.mulVec_mulVec]

/-- The inverse actual Norton word has this exact integral basis action. -/
theorem monsterNortonUInverseIntegralAction_basis (z : Fin 24 → ℤ) :
    (monsterNortonUFiber⁻¹).val.2.val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding
          (leechBasisMatrix *ᵥ (monsterNortonUInverseIntegralAction *ᵥ z)) := by
  change (monsterNortonUFiber.val.2⁻¹).val _ = _
  rw [monsterNortonUFiber_leech, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev,
    inv_inv, inv_inv]
  change (co1XiIsometry⁻¹).val ((omegaOrbitPermutationIsometry 1).val
    ((co1XiIsometry⁻¹).val ((omegaOrbitPermutationIsometry 0).val
      ((monsterSourceY82Isometry⁻¹).val
        (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))))) = _
  have hy : (monsterSourceY82Isometry⁻¹).val = monsterSourceY82Isometry.val := by rfl
  have hp (k : Fin 2) (t : Fin 24 → ℤ) : (omegaOrbitPermutationIsometry k).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ t)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ
          (omegaOrbitIntegralMatrices (Fin.natAdd 2 k) *ᵥ t)) := by
    have h := omegaOrbitMonomial_basis (Fin.natAdd 2 k) t
    fin_cases k <;> exact h
  rw [hy, monsterSourceY82_embedding_basis, hp, xi_inverse_basis, hp, xi_inverse_basis]
  simp only [monsterNortonUInverseIntegralAction, Matrix.mulVec_mulVec, mul_assoc]
  rfl

/-- Arbitrary inverse powers have genuine integral matrix powers, without an order assumption. -/
theorem monsterNortonUInverseIntegralAction_power_basis (n : ℕ) (z : Fin 24 → ℤ) :
    ((monsterNortonUFiber⁻¹) ^ n).val.2.val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding
          (leechBasisMatrix *ᵥ ((monsterNortonUInverseIntegralAction ^ n) *ᵥ z)) :=
  basis_power (monsterNortonUFiber⁻¹).val.2 _ monsterNortonUInverseIntegralAction_basis n z

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
