/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortCoordinateRecognition
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Matrix form of short-coordinate recognition, with the physical action
`u ↦ R.mulVec u` and square action `A ↦ R * A * R.transpose`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The real equivalence associated to an orthogonal matrix, with transpose inverse. -/
noncomputable def shortCoordinateOrthogonalEquiv
    (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hTR : R.transpose * R = 1) (hRT : R * R.transpose = 1) :
    (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) :=
  Matrix.toLin'OfInv hTR hRT

/-- Its forward action uses the stated column-vector convention. -/
theorem shortCoordinateOrthogonalEquiv_apply
    (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hTR : R.transpose * R = 1) (hRT : R * R.transpose = 1)
    (u : Fin 24 → ℝ) : shortCoordinateOrthogonalEquiv R hTR hRT u = R *ᵥ u := rfl

/-- Matrix orthogonality gives the physical real pairing identity. -/
theorem shortCoordinateOrthogonalEquiv_pairing
    (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hTR : R.transpose * R = 1) (hRT : R * R.transpose = 1)
    (u v : Fin 24 → ℝ) :
    stdPairingFun (shortCoordinateOrthogonalEquiv R hTR hRT u)
      (shortCoordinateOrthogonalEquiv R hTR hRT v) = stdPairingFun u v := by
  change (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ v
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hTR, Matrix.vecMul_one]

/-- Conjugating an outer square gives the outer square of the physical image. -/
theorem shortCoordinateRecognition_conjugate_outer
    (R : Matrix (Fin 24) (Fin 24) ℝ) (u : Fin 24 → ℝ) :
    R * Matrix.vecMulVec u u * R.transpose =
      Matrix.vecMulVec (R *ᵥ u) (R *ᵥ u) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- A coordinate unit has exactly its corresponding physical outer square. -/
theorem shortCoordinateSquare_unit (r : GriessShortIndex) :
    shortCoordinateSquare (shortCoordinateUnit r) =
      Matrix.vecMulVec (griessShortVector r) (griessShortVector r) := by
  classical
  simp [shortCoordinateSquare, shortCoordinateUnit, Pi.single_apply]

/-- The required matrix identity only needs to be proved on coordinate units.
It forces the same label permutation on the coordinate and physical actions,
and recognizes the physical map as an actual Leech lattice isometry. -/
theorem shortCoordinateRecognition_matrix_basis
    (F : (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ))
    (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hF : ∀ X Y, (∑ r, F X r * F Y r) = ∑ r, X r * Y r)
    (hTR : R.transpose * R = 1) (hRT : R * R.transpose = 1)
    (hsquare : ∀ r, shortCoordinateSquare (F (shortCoordinateUnit r)) =
      R * Matrix.vecMulVec (griessShortVector r) (griessShortVector r) * R.transpose) :
    (∃ p : Equiv.Perm GriessShortIndex, ∀ r,
      (F (shortCoordinateUnit r) = shortCoordinateUnit (p r) ∨
        F (shortCoordinateUnit r) = -shortCoordinateUnit (p r)) ∧
      (R *ᵥ griessShortVector r = griessShortVector (p r) ∨
        R *ᵥ griessShortVector r = -griessShortVector (p r))) ∧
      shortCoordinateOrthogonalEquiv R hTR hRT ∈ leechIsomSubgroup := by
  have hb (r : GriessShortIndex) : shortCoordinateSquare (F (shortCoordinateUnit r)) =
      Matrix.vecMulVec (shortCoordinateOrthogonalEquiv R hTR hRT (griessShortVector r))
        (shortCoordinateOrthogonalEquiv R hTR hRT (griessShortVector r)) := by
    rw [hsquare r, shortCoordinateRecognition_conjugate_outer]
    rfl
  exact ⟨shortCoordinateRecognition_signed_permutation F
    (shortCoordinateOrthogonalEquiv R hTR hRT) hF
    (shortCoordinateOrthogonalEquiv_pairing R hTR hRT) hb,
    shortCoordinateRecognition_mem_isometry F (shortCoordinateOrthogonalEquiv R hTR hRT)
      hF (shortCoordinateOrthogonalEquiv_pairing R hTR hRT) hb⟩

/-- The full matrix-square identity implies the basis identity used by recognition. -/
theorem shortCoordinateRecognition_matrix_square
    (F : (GriessShortIndex → ℝ) ≃ₗ[ℝ] (GriessShortIndex → ℝ))
    (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hF : ∀ X Y, (∑ r, F X r * F Y r) = ∑ r, X r * Y r)
    (hTR : R.transpose * R = 1) (hRT : R * R.transpose = 1)
    (hsquare : ∀ X, shortCoordinateSquare (F X) =
      R * shortCoordinateSquare X * R.transpose) :
    (∃ p : Equiv.Perm GriessShortIndex, ∀ r,
      (F (shortCoordinateUnit r) = shortCoordinateUnit (p r) ∨
        F (shortCoordinateUnit r) = -shortCoordinateUnit (p r)) ∧
      (R *ᵥ griessShortVector r = griessShortVector (p r) ∨
        R *ᵥ griessShortVector r = -griessShortVector (p r))) ∧
      shortCoordinateOrthogonalEquiv R hTR hRT ∈ leechIsomSubgroup := by
  apply shortCoordinateRecognition_matrix_basis F R hF hTR hRT
  intro r
  simpa only [shortCoordinateSquare_unit] using hsquare (shortCoordinateUnit r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
