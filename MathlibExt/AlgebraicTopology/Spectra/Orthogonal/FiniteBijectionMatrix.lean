/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.MatrixIndex
public import MathlibExt.CategoryTheory.Operad.FinBijDegreeInclusion
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite bijections as orthogonal coordinate matrices

The matrix is obtained from the original equivalence between full orthogonal
matrices and linear isometric equivalences. Its action is the actual coordinate
permutation, with both rectangular inverse equations retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Matrix

namespace CategoryTheory.Spectra

/-- The orthogonal matrix of the actual finite-coordinate isometry. -/
def finiteBijectionMatrix {m n : ℕ} (e : Fin m ≃ Fin n) :
    OrthogonalMatrixHom m n :=
  (OrthogonalMatrixHom.equivLinearIsometryEquiv m n).symm
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)

/-- The matrix represents the original coordinate linear isometry. -/
theorem finiteBijectionMatrix_isometry {m n : ℕ} (e : Fin m ≃ Fin n) :
    OrthogonalMatrixHom.equivLinearIsometryEquiv m n (finiteBijectionMatrix e) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e :=
  (OrthogonalMatrixHom.equivLinearIsometryEquiv m n).apply_symm_apply _

/-- Literal entries put the source coordinate `j` into the target coordinate `e j`. -/
theorem finiteBijectionMatrix_apply {m n : ℕ} (e : Fin m ≃ Fin n)
    (i : Fin n) (j : Fin m) :
    (finiteBijectionMatrix e).1 i j = if i = e j then 1 else 0 := by
  change ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toLinearEquiv.toLinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) i j = _
  rw [LinearMap.toMatrix_apply]
  change (EuclideanSpace.basisFun (Fin n) ℝ).repr
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
        ((EuclideanSpace.basisFun (Fin m) ℝ) j)) i = _
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, PiLp.single_apply]

/-- The canonical matrix is exactly the original row reindexing of the identity. -/
theorem finiteBijectionMatrix_reindex {m n : ℕ} (e : Fin m ≃ Fin n) :
    (finiteBijectionMatrix e).1 =
      Matrix.reindex e (Equiv.refl (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ) := by
  ext i j
  rw [finiteBijectionMatrix_apply]
  simp [Matrix.reindex_apply, Matrix.one_apply, Equiv.symm_apply_eq]

/-- Matrix evaluation is the original coordinate permutation. -/
theorem finiteBijectionMatrix_mulVec {m n : ℕ} (e : Fin m ≃ Fin n)
    (x : Fin m → ℝ) :
    (finiteBijectionMatrix e).1 *ᵥ x = x ∘ e.symm := by
  rw [finiteBijectionMatrix_reindex]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.one_apply]

/-- Source-first composition of finite coordinate matrices. -/
theorem finiteBijectionMatrix_comp {m n p : ℕ}
    (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin p) :
    OrthogonalMatrixHom.comp (finiteBijectionMatrix e) (finiteBijectionMatrix f) =
      finiteBijectionMatrix (e.trans f) := by
  apply OrthogonalMatrixHom.ext
  ext i j
  simp only [OrthogonalMatrixHom.comp, Matrix.mul_apply, finiteBijectionMatrix_apply,
    Equiv.trans_apply]
  simp
  rfl

/-- The finite identity becomes the actual orthogonal identity matrix. -/
@[simp]
theorem finiteBijectionMatrix_refl (m : ℕ) :
    finiteBijectionMatrix (Equiv.refl (Fin m)) = OrthogonalMatrixHom.id m := by
  apply OrthogonalMatrixHom.ext
  ext i j
  simp [finiteBijectionMatrix_apply, OrthogonalMatrixHom.id, Matrix.one_apply]
  rfl

/-- Transpose is the matrix associated with the inverse finite bijection. -/
theorem finiteBijectionMatrix_symm {m n : ℕ} (e : Fin m ≃ Fin n) :
    OrthogonalMatrixHom.transpose (finiteBijectionMatrix e) =
      finiteBijectionMatrix e.symm := by
  apply OrthogonalMatrixHom.ext
  ext i j
  simp [OrthogonalMatrixHom.transpose, Matrix.transpose_apply, finiteBijectionMatrix_apply,
    Equiv.eq_symm_apply, eq_comm]

/-- The matrix constructor includes both inverse equations, with no equal-dimension cast. -/
theorem finiteBijectionMatrix_inverse_equations {m n : ℕ} (e : Fin m ≃ Fin n) :
    (finiteBijectionMatrix e).1.transpose * (finiteBijectionMatrix e).1 = 1 ∧
      (finiteBijectionMatrix e).1 * (finiteBijectionMatrix e).1.transpose = 1 :=
  (finiteBijectionMatrix e).2

/-- The actual finite-coordinate bijection of a morphism in the original small symmetric index. -/
abbrev smallFiniteBijection {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    Fin A.of.len ≃ Fin B.of.len :=
  Operad.SmallFinBijGroupoid.smallEquivOfHom f
theorem smallFiniteBijection_id (A : Operad.SmallFinBijGroupoid) :
    smallFiniteBijection (𝟙 A) = Equiv.refl (Fin A.of.len) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_id A
theorem smallFiniteBijection_comp {A B C : Operad.SmallFinBijGroupoid}
    (f : A ⟶ B) (g : B ⟶ C) :
    smallFiniteBijection (f ≫ g) =
      (smallFiniteBijection f).trans (smallFiniteBijection g) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_comp f g

/-- Every original symmetric-index morphism has its actual coordinate orthogonal matrix. -/
def smallBijectionMatrix {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    OrthogonalMatrixHom A.of.len B.of.len :=
  finiteBijectionMatrix (smallFiniteBijection f)

/-- Original symmetric identity maps to the original orthogonal matrix identity. -/
@[simp]
theorem smallBijectionMatrix_id (A : Operad.SmallFinBijGroupoid) :
    smallBijectionMatrix (𝟙 A) = OrthogonalMatrixHom.id A.of.len := by
  rw [smallBijectionMatrix, smallFiniteBijection_id, finiteBijectionMatrix_refl]

/-- Original symmetric composition maps to the original orthogonal matrix composition. -/
theorem smallBijectionMatrix_comp {A B C : Operad.SmallFinBijGroupoid}
    (f : A ⟶ B) (g : B ⟶ C) :
    smallBijectionMatrix (f ≫ g) =
      OrthogonalMatrixHom.comp (smallBijectionMatrix f) (smallBijectionMatrix g) := by
  rw [smallBijectionMatrix, smallFiniteBijection_comp, ← finiteBijectionMatrix_comp]
  rfl

end CategoryTheory.Spectra
