/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Whole rational matrices and integral basis certificates construct genuine Co0 lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A real orthogonal matrix retains its complete transpose inverse. -/
def generatedTwelfthMatrixEquiv (m : Matrix (Fin 24) (Fin 24) ℝ)
    (hl : m.transpose * m = 1) (hr : m * m.transpose = 1) :
    (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) where
  toFun := m.mulVec
  invFun := m.transpose.mulVec
  left_inv x := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
  right_inv x := by rw [Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

private theorem basis_mem (m : Matrix (Fin 24) (Fin 24) ℝ)
    (c : Matrix (Fin 24) (Fin 24) ℤ)
    (hb : m * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) * c.map (Int.castRingHom ℝ))
    (x : Fin 24 → ℝ) (hx : x ∈ LeechLattice) : m *ᵥ x ∈ LeechLattice := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨v, hv⟩ := leechExplicitCoordinateMap_bijective.2 ⟨u, hu⟩
  have hh : leechBasisMatrix *ᵥ v = u := congrArg Subtype.val hv
  rw [← hh, leechCoordinateEmbedding_mulVec, Matrix.mulVec_mulVec, hb,
    ← Matrix.mulVec_mulVec, ← leechCoordinateEmbedding_mulVec,
    ← leechCoordinateEmbedding_mulVec]
  exact Submodule.mem_map.mpr ⟨_, (leechExplicitCoordinateMap (c *ᵥ v)).property, rfl⟩

/-- Integral inverse basis matrices certify both physical orientations. -/
theorem generatedTwelfth_matrix_inverse_basis (m : Matrix (Fin 24) (Fin 24) ℝ)
    (c ci : Matrix (Fin 24) (Fin 24) ℤ) (hl : m.transpose * m = 1)
    (hb : m * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) * c.map (Int.castRingHom ℝ))
    (hi : c * ci = 1) :
    m.transpose * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) * ci.map (Int.castRingHom ℝ) := by
  have hc := congrArg (Int.castRingHom ℝ).mapMatrix hi
  simp only [map_mul, map_one] at hc
  change c.map (Int.castRingHom ℝ) * ci.map (Int.castRingHom ℝ) = 1 at hc
  calc
    _ = m.transpose * (leechBasisMatrix.map (Int.castRingHom ℝ) *
        (c.map (Int.castRingHom ℝ) * ci.map (Int.castRingHom ℝ))) := by rw [hc, mul_one]
    _ = (m.transpose * (leechBasisMatrix.map (Int.castRingHom ℝ) *
        c.map (Int.castRingHom ℝ))) * ci.map (Int.castRingHom ℝ) := by simp [mul_assoc]
    _ = (m.transpose * (m * leechBasisMatrix.map (Int.castRingHom ℝ))) *
        ci.map (Int.castRingHom ℝ) := by rw [← hb]
    _ = _ := by rw [← mul_assoc m.transpose, hl, one_mul]

/-- Full orthogonal physical and integral basis certificates construct a genuine lattice lift. -/
def generatedTwelfthMatrixIsometry (m : Matrix (Fin 24) (Fin 24) ℝ)
    (c ci : Matrix (Fin 24) (Fin 24) ℤ)
    (hl : m.transpose * m = 1) (hr : m * m.transpose = 1)
    (hb : m * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) * c.map (Int.castRingHom ℝ))
    (hi : c * ci = 1) : leechIsomSubgroup :=
  ⟨generatedTwelfthMatrixEquiv m hl hr, by
    constructor
    · intro x y
      change (m *ᵥ x) ⬝ᵥ (m *ᵥ y) = x ⬝ᵥ y
      rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
        hl, Matrix.one_mulVec, dotProduct_comm]
    · intro x
      constructor
      · exact basis_mem m c hb x
      · intro hx
        have hh := basis_mem m.transpose ci
          (generatedTwelfth_matrix_inverse_basis m c ci hl hb hi) _ hx
        change m.transpose *ᵥ (m *ᵥ x) ∈ LeechLattice at hh
        rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec] at hh
        exact hh⟩

/-- The certificate constructor retains the exact full matrix on every real vector. -/
theorem generatedTwelfth_matrix_isometry_apply (m : Matrix (Fin 24) (Fin 24) ℝ)
    (c ci : Matrix (Fin 24) (Fin 24) ℤ) (hl hr hb hi) (x : Fin 24 → ℝ) :
    (generatedTwelfthMatrixIsometry m c ci hl hr hb hi).val x = m *ᵥ x := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
