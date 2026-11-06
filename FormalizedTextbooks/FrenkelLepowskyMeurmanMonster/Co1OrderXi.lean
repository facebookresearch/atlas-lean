/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiData

/-! The real three-bases lattice isometry from the checked rational certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- The real matrix obtained from the exact rational formula. -/
noncomputable def co1XiMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  co1XiMatrixQ.map (Rat.castHom ℝ)

theorem co1Xi_cube : co1XiMatrix * co1XiMatrix * co1XiMatrix = 1 := by
  have h := congrArg (Rat.castHom ℝ).mapMatrix co1Xi_cube_certificate
  rw [map_mul, map_mul, map_one] at h
  exact h

theorem co1Xi_orthogonal : co1XiMatrix.transpose * co1XiMatrix = 1 := by
  have h := congrArg (Rat.castHom ℝ).mapMatrix co1Xi_orthogonal_certificate
  rw [map_mul, map_one] at h
  exact h

theorem co1Xi_basis_real :
    co1XiMatrix * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) * co1XiBasisMatrix.map (Int.castRingHom ℝ) := by
  have h := congrArg (Rat.castHom ℝ).mapMatrix co1Xi_basis_certificate
  have hcast (A : Matrix (Fin 24) (Fin 24) ℤ) :
      (A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) = A.map (Int.castRingHom ℝ) := by
    ext i j
    simp
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at h
  rw [hcast, hcast] at h
  exact h

/-- Column action of the physical three-bases transformation, with its cube inverse. -/
noncomputable def co1XiEquiv : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) where
  toFun := co1XiMatrix.mulVec
  invFun := (co1XiMatrix * co1XiMatrix).mulVec
  left_inv x := by rw [Matrix.mulVec_mulVec, co1Xi_cube, Matrix.one_mulVec]
  right_inv x := by rw [Matrix.mulVec_mulVec, ← mul_assoc, co1Xi_cube, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

@[simp] theorem co1XiEquiv_apply (x : Fin 24 → ℝ) : co1XiEquiv x = co1XiMatrix *ᵥ x := rfl

@[simp] theorem co1XiEquiv_symm_apply (x : Fin 24 → ℝ) :
    co1XiEquiv.symm x = (co1XiMatrix * co1XiMatrix) *ᵥ x := rfl

/-- The other physical orientation is the square of the constructed matrix. -/
theorem co1XiMatrix_square_eq_transpose : co1XiMatrix * co1XiMatrix = co1XiMatrix.transpose := by
  calc
    co1XiMatrix * co1XiMatrix = 1 * (co1XiMatrix * co1XiMatrix) := (one_mul _).symm
    _ = (co1XiMatrix.transpose * co1XiMatrix) * (co1XiMatrix * co1XiMatrix) := by
      rw [co1Xi_orthogonal]
    _ = co1XiMatrix.transpose * (co1XiMatrix * (co1XiMatrix * co1XiMatrix)) := mul_assoc _ _ _
    _ = co1XiMatrix.transpose := by
      rw [← mul_assoc co1XiMatrix co1XiMatrix co1XiMatrix, co1Xi_cube, mul_one]

/-- Normalization intertwines every integer coordinate matrix with its real matrix. -/
theorem leechCoordinateEmbedding_mulVec (A : Matrix (Fin 24) (Fin 24) ℤ)
    (u : Fin 24 → ℤ) :
    leechCoordinateEmbedding (A *ᵥ u) =
      A.map (Int.castRingHom ℝ) *ᵥ leechCoordinateEmbedding u := by
  ext i
  simp only [leechCoordinateEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Matrix.map_apply,
    Finset.sum_div, mul_div_assoc]
  rfl

/-- The checked certificate makes the source matrix act on the actual integral basis. -/
theorem co1Xi_embedding_basis (u : Fin 24 → ℤ) :
    co1XiEquiv (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (co1XiBasisMatrix *ᵥ u)) := by
  rw [co1XiEquiv_apply, leechCoordinateEmbedding_mulVec,
    Matrix.mulVec_mulVec, co1Xi_basis_real, ← Matrix.mulVec_mulVec,
    ← leechCoordinateEmbedding_mulVec, ← leechCoordinateEmbedding_mulVec]

/-- The three-bases matrix carries the actual Leech lattice into itself. -/
theorem co1Xi_mem (x : Fin 24 → ℝ) (hx : x ∈ LeechLattice) : co1XiEquiv x ∈ LeechLattice := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨v, hv⟩ := leechExplicitCoordinateMap_bijective.2 ⟨u, hu⟩
  have hh : leechBasisMatrix *ᵥ v = u := congrArg Subtype.val hv
  rw [← hh, co1Xi_embedding_basis]
  exact Submodule.mem_map.mpr
    ⟨_, (leechExplicitCoordinateMap (co1XiBasisMatrix *ᵥ v)).property, rfl⟩

/-- The source three-bases column transformation is a genuine lattice isometry. -/
noncomputable def co1XiIsometry : leechIsomSubgroup :=
  ⟨co1XiEquiv, by
    constructor
    · intro x y
      change (co1XiMatrix *ᵥ x) ⬝ᵥ (co1XiMatrix *ᵥ y) = x ⬝ᵥ y
      rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
        co1Xi_orthogonal, Matrix.one_mulVec, dotProduct_comm]
    · intro x
      constructor
      · exact co1Xi_mem x
      · intro hx
        have hh := co1Xi_mem _ (co1Xi_mem _ hx)
        change co1XiMatrix *ᵥ (co1XiMatrix *ᵥ (co1XiMatrix *ᵥ x)) ∈ LeechLattice at hh
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, co1Xi_cube,
          Matrix.one_mulVec] at hh
        exact hh⟩

/-- Both orientations have order dividing three in the actual Co₀ group. -/
theorem co1XiIsometry_cube : co1XiIsometry ^ 3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change co1XiMatrix *ᵥ (co1XiMatrix *ᵥ (co1XiMatrix *ᵥ x)) = x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, co1Xi_cube, Matrix.one_mulVec]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
