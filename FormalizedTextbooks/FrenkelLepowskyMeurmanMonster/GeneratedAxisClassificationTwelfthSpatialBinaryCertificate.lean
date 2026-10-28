/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Actual complete physical numerator matrices determine genuine lattice binary actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine integral lattice embedding retains every natural scalar in real coordinates. -/
theorem generatedTwelfth_embedding_nat_smul (d : ℕ) (u : Fin 24 → ℤ) :
    leechCoordinateEmbedding ((d : ℤ) • u) =
      (d : ℝ) • leechCoordinateEmbedding u := by
  ext i
  simp only [leechCoordinateEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  ring

/-- A complete actual physical matrix and integral change of basis give the real basis action. -/
theorem generatedTwelfth_spatial_integral_basis_of_matrix
    (e : leechIsomSubgroup) (n c : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd : d ≠ 0)
    (hphysical : (d : ℝ) • leechIsomMatrix e = n.map (Int.castRingHom ℝ))
    (hbasis : n * leechBasisMatrix = (d : ℤ) • (leechBasisMatrix * c))
    (z : Fin 24 → ℤ) :
    e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (c *ᵥ z)) := by
  have h : (d : ℝ) • e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      (d : ℝ) • leechCoordinateEmbedding (leechBasisMatrix *ᵥ (c *ᵥ z)) := by
    rw [← leechIsomMatrix_mulVec, ← Matrix.smul_mulVec, hphysical,
      ← leechCoordinateEmbedding_mulVec, Matrix.mulVec_mulVec, hbasis,
      Matrix.smul_mulVec, generatedTwelfth_embedding_nat_smul, ← Matrix.mulVec_mulVec]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  ext i
  exact mul_left_cancel₀ hd' (congrFun h i)

/-- Exact complete physical and integral certificates bind all24 actual binary coordinates. -/
theorem generatedTwelfth_spatial_binary_of_matrix
    (e : leechIsomSubgroup) (n c : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd : d ≠ 0)
    (hphysical : (d : ℝ) • leechIsomMatrix e = n.map (Int.castRingHom ℝ))
    (hbasis : n * leechBasisMatrix = (d : ℤ) • (leechBasisMatrix * c))
    (v : Fin 24 → ZMod 2) :
    leechBinaryAction e v =
      (leechHyperbolicInverse * c.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ v :=
  leechBinaryAction_of_basis_certificate e c
    (generatedTwelfth_spatial_integral_basis_of_matrix e n c d hd hphysical hbasis) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
