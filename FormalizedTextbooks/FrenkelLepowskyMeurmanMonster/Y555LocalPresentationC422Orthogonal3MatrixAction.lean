/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite matrix action and norm characterize the independent Cartan isometry group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ReflectionForm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Equality of actual vector actions identifies invertible finite coordinate matrices. -/
theorem y422Orthogonal3GL_ext (g h : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3))
    (action : ∀ v : Fin 8 → ZMod 3, g.val *ᵥ v = h.val *ᵥ v) : g = h := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  exact action (Pi.single i 1)

/-- The independent bilinear pairing under a finite matrix has its exact congruence matrix. -/
theorem y422Orthogonal3Matrix_pairing (matrix : Matrix (Fin 8) (Fin 8) (ZMod 3))
    (v w : Fin 8 → ZMod 3) :
    y422Orthogonal3Pairing (matrix *ᵥ v) (matrix *ᵥ w) =
      dotProduct v ((matrix.transpose * y422Orthogonal3Gram * matrix) *ᵥ w) := by
  change dotProduct (matrix *ᵥ v) (y422Orthogonal3Gram *ᵥ (matrix *ᵥ w)) = _
  rw [dotProduct_comm (matrix *ᵥ v), ← Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Preserving the exact quadratic norm implies membership in the full isometry group. -/
theorem y422Orthogonal3FullGroup_mem_of_norm
    (g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3))
    (norm : ∀ v : Fin 8 → ZMod 3,
      y422Orthogonal3VectorNorm (g.val *ᵥ v) = y422Orthogonal3VectorNorm v) :
    g ∈ y422Orthogonal3FullGroup := by
  have hp (v w : Fin 8 → ZMod 3) :
      y422Orthogonal3Pairing (g.val *ᵥ v) (g.val *ᵥ w) = y422Orthogonal3Pairing v w := by
    rw [y422Orthogonal3Pairing_polarization, ← Matrix.mulVec_add]
    rw [norm, norm, norm]
    exact (y422Orthogonal3Pairing_polarization v w).symm
  change g.val.transpose * y422Orthogonal3Gram * g.val = y422Orthogonal3Gram
  ext r c
  have h := hp (Pi.single r 1) (Pi.single c 1)
  rw [y422Orthogonal3Matrix_pairing] at h
  change dotProduct (Pi.single r 1)
      ((g.val.transpose * y422Orthogonal3Gram * g.val) *ᵥ Pi.single c 1) =
    dotProduct (Pi.single r 1) (y422Orthogonal3Gram *ᵥ Pi.single c 1) at h
  simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
