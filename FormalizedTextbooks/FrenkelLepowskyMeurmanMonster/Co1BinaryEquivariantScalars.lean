/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryEquivariantRankOne
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleSubspaces

/-! The genuine binary Conway module has only scalar equivariant endomorphisms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A generator-equivariant endomorphism acts as a scalar on the genuine cyclic vector. -/
theorem co1Binary_equivariant_column_scalar
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1BinaryCommutes T (omegaOrbitBinaryMatrices k)) :
    ∃ a : ZMod 2, T co1IrreducibleColumn = a • co1IrreducibleColumn := by
  let x : Fin 24 → ZMod 2 := Pi.single 0 1
  have hr : co1IrreducibleRow ⬝ᵥ x = 1 := by
    change co1IrreducibleRow ⬝ᵥ (Pi.single 0 1) = 1
    decide +kernel
  have hm : co1IrreducibleStage 28 =
      Matrix.vecMulVec co1IrreducibleColumn co1IrreducibleRow :=
    Matrix.ext co1Irreducible_rank_one
  have h := co1Binary_rank_one_commutes T hG x
  rw [hm, Matrix.vecMulVec_mulVec, hr, Matrix.vecMulVec_mulVec] at h
  simp only [op_smul_eq_smul, one_smul] at h
  exact ⟨co1IrreducibleRow ⬝ᵥ T x, h⟩

/-- Commutation with the five original generators forces every endomorphism to be scalar. -/
theorem co1Binary_generator_equivariant_scalar
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1BinaryCommutes T (omegaOrbitBinaryMatrices k)) :
    ∃ a : ZMod 2, T = a • LinearMap.id := by
  obtain ⟨a, ha⟩ := co1Binary_equivariant_column_scalar T hG
  let S : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
    T - a • LinearMap.id
  have hS (k : Fin 5) : co1BinaryCommutes S (omegaOrbitBinaryMatrices k) := by
    intro x
    change T (omegaOrbitBinaryMatrices k *ᵥ x) - a • (omegaOrbitBinaryMatrices k *ᵥ x) =
      omegaOrbitBinaryMatrices k *ᵥ (T x - a • x)
    rw [hG k, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hK : ∀ k : Fin 5,
      co1IrreduciblePreserves (LinearMap.ker S) (omegaOrbitBinaryMatrices k) := by
    intro k x hx
    change S (omegaOrbitBinaryMatrices k *ᵥ x) = 0
    rw [hS k, show S x = 0 from hx, Matrix.mulVec_zero]
  have hc : co1IrreducibleColumn ∈ LinearMap.ker S := by
    change T co1IrreducibleColumn - a • co1IrreducibleColumn = 0
    rw [ha, sub_self]
  have ht := co1Irreducible_column_mem_top (LinearMap.ker S) hK hc
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  have hx : x ∈ LinearMap.ker S := by rw [ht]; trivial
  have he : T x - a • x = 0 := hx
  exact sub_eq_zero.mp he

/-- Every linear endomorphism commuting with the actual full Conway action is scalar. -/
theorem co1BinaryAction_equivariant_scalar
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hT : ∀ g : Co1, ∀ x, T (co1BinaryAction g x) = co1BinaryAction g (T x)) :
    ∃ a : ZMod 2, T = a • LinearMap.id := by
  apply co1Binary_generator_equivariant_scalar T
  intro k x
  have h := hT (QuotientGroup.mk' signsSubgroup (omegaOrbitIsometry k)) x
  change T (leechBinaryAction (omegaOrbitIsometry k) x) =
    leechBinaryAction (omegaOrbitIsometry k) (T x) at h
  simpa only [omegaOrbitIsometry_binary] using h

/-- Over the actual binary field, the only equivariant endomorphisms are zero and identity. -/
theorem co1BinaryAction_equivariant_zero_or_id
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hT : ∀ g : Co1, ∀ x, T (co1BinaryAction g x) = co1BinaryAction g (T x)) :
    T = 0 ∨ T = LinearMap.id := by
  obtain ⟨a, ha⟩ := co1BinaryAction_equivariant_scalar T hT
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  rcases hbits a with hz | ho
  · left; simpa only [hz, zero_smul] using ha
  · right; simpa only [ho, one_smul] using ha

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
