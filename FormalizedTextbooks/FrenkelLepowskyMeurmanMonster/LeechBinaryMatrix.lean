/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Matrix certificates for the actual lattice action on Λ/2Λ. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Source coordinates are parity in the actual integral basis, followed by
its checked binary change of basis. -/
theorem leechHyperbolicCoordinates_explicit (u : leechIntegral) :
    leechHyperbolicCoordinates (leechReduction u) =
      leechHyperbolicInverse *ᵥ integerParity (leechExplicitCoordinates u) := by
  rfl

/-- Integer matrix multiplication reduces to binary matrix multiplication. -/
theorem integerParity_mulVec (C : Matrix (Fin 24) (Fin 24) ℤ) (u : Fin 24 → ℤ) :
    integerParity (C *ᵥ u) = C.map (Int.castRingHom (ZMod 2)) *ᵥ integerParity u := by
  ext i
  simp only [integerParity, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec,
    dotProduct, Int.cast_sum, Int.cast_mul, Matrix.map_apply]
  rfl

/-- A verified integral basis action is the actual induced lattice action. -/
theorem leechIntegralAction_coordinates_of_basis_certificate
    (e : leechIsomSubgroup) (C : Matrix (Fin 24) (Fin 24) ℤ)
    (he : ∀ z : Fin 24 → ℤ,
      e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (C *ᵥ z)))
    (u : leechIntegral) :
    leechExplicitCoordinates (leechIntegralAction e u) = C *ᵥ leechExplicitCoordinates u := by
  have h : leechIntegralAction e u =
      leechExplicitCoordinateMap (C *ᵥ leechExplicitCoordinates u) := by
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding, ← leechExplicitCoordinates_vector u, he]
    rfl
  rw [h]
  exact leechExplicitCoordinates.apply_symm_apply _

private theorem matrix_transport_mulVec {R : Type*} [Semiring R]
    (A B C D : Matrix (Fin 24) (Fin 24) R) (hCD : C * D = 1) (z : Fin 24 → R) :
    (A * B * C) *ᵥ (D *ᵥ z) = A *ᵥ (B *ᵥ z) := by
  simp only [Matrix.mulVec_mulVec, mul_assoc, hCD, mul_one]

/-- The binary action matrix is determined by a checked action on the actual
integral lattice basis. No modular action is introduced as independent data. -/
theorem leechBinaryAction_of_basis_certificate
    (e : leechIsomSubgroup) (C : Matrix (Fin 24) (Fin 24) ℤ)
    (he : ∀ z : Fin 24 → ℤ,
      e.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (C *ᵥ z)))
    (v : Fin 24 → ZMod 2) :
    leechBinaryAction e v =
      (leechHyperbolicInverse * C.map (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix) *ᵥ v := by
  obtain ⟨w, rfl⟩ := leechHyperbolicCoordinates.surjective v
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective twiceLeechIntegral w
  rw [leechBinaryAction_coordinates]
  change leechHyperbolicCoordinates (leechReduction (leechIntegralAction e u)) =
    (leechHyperbolicInverse * C.map (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix) *ᵥ
      leechHyperbolicCoordinates (leechReduction u)
  rw [leechHyperbolicCoordinates_explicit,
    leechIntegralAction_coordinates_of_basis_certificate e C he,
    integerParity_mulVec, leechHyperbolicCoordinates_explicit]
  exact (matrix_transport_mulVec leechHyperbolicInverse
    (C.map (Int.castRingHom (ZMod 2))) leechHyperbolicMatrix leechHyperbolicInverse
    leechHyperbolicMatrix_inverse.1 (integerParity (leechExplicitCoordinates u))).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
