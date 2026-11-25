/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Finite square C-star matrix padding

The map retains the original entries through the actual finite index
embedding and is nonunital. Its C-star specialization preserves the actual
operator norm, including empty source stages and zero coefficient algebras.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarMatrix

universe u

/-- Let `A` be a possibly nonunital ring. `A` has a complex module structure. `A` has an additive star
involution. For natural numbers `n` and `m`. Assume `n ≤ m`. Top-left finite padding, with the
existing matrix zero-extension value, bundled as a nonunital complex star-algebra homomorphism.
-/
def zeroExtendStarAlgHom
    {A : Type u} [NonUnitalRing A] [Module ℂ A] [StarAddMonoid A]
    {n m : ℕ} (h : n ≤ m) :
    CStarMatrix (Fin n) (Fin n) A →⋆ₙₐ[ℂ] CStarMatrix (Fin m) (Fin m) A where
  toFun X := ofMatrix (Matrix.zeroExtend h (ofMatrix.symm X))
  map_zero' := by
    change ofMatrix ((Matrix.zeroExtendAlgHom (k := ℂ) (A := A) h) 0) = 0
    rw [map_zero, of_zero]
  map_add' X Y := by
    change ofMatrix ((Matrix.zeroExtendAlgHom (k := ℂ) (A := A) h)
      (ofMatrix.symm X + ofMatrix.symm Y)) =
      ofMatrix ((Matrix.zeroExtendAlgHom (k := ℂ) (A := A) h) (ofMatrix.symm X)) +
        ofMatrix ((Matrix.zeroExtendAlgHom (k := ℂ) (A := A) h) (ofMatrix.symm Y))
    rw [map_add]
    rfl
  map_smul' z X := by
    change ofMatrix ((Matrix.zeroExtendAlgHom (k := ℂ) (A := A) h)
      (z • ofMatrix.symm X)) =
      z • ofMatrix ((Matrix.zeroExtendAlgHom (k := ℂ) (A := A) h) (ofMatrix.symm X))
    rw [map_smul]
    rfl
  map_mul' X Y := by
    change ofMatrix (Matrix.zeroExtend h (ofMatrix.symm (X * Y))) =
      ofMatrix (Matrix.zeroExtend h (ofMatrix.symm X)) *
        ofMatrix (Matrix.zeroExtend h (ofMatrix.symm Y))
    rw [ofMatrix_symm_mul, Matrix.zeroExtend_mul, of_mul_of]
  map_star' X := by
    apply CStarMatrix.ext
    intro i j
    change Matrix.zeroExtend h (ofMatrix.symm (star X)) i j =
      star (Matrix.zeroExtend h (ofMatrix.symm X) j i)
    by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
      simp only [Matrix.zeroExtend_apply, hi, hj, ↓reduceDIte,
        ofMatrix_symm_apply, CStarMatrix.star_apply, star_zero]

/-- Let `A` be a possibly nonunital ring. `A` has a complex module structure. `A` has an additive star
involution. For natural numbers `n` and `m` and `X : CStarMatrix (Fin n) (Fin n) A`. Assume `n ≤ m`.
The bundled padding map has exactly the existing matrix zero-extension value.
-/
@[simp]
theorem zeroExtendStarAlgHom_apply
    {A : Type u} [NonUnitalRing A] [Module ℂ A] [StarAddMonoid A]
    {n m : ℕ} (h : n ≤ m) (X : CStarMatrix (Fin n) (Fin n) A) :
    zeroExtendStarAlgHom h X = ofMatrix (Matrix.zeroExtend h (ofMatrix.symm X)) :=
  rfl

/-- Let `A` be a possibly nonunital ring. `A` has a complex module structure. `A` has an additive star
involution. For natural numbers `n` and `m`, `X : CStarMatrix (Fin n) (Fin n) A` and `i` and `j :
Fin m`. Assume `n ≤ m`. Padding retains every entry and makes the added rows and columns zero.
-/
theorem zeroExtendStarAlgHom_apply_entry
    {A : Type u} [NonUnitalRing A] [Module ℂ A] [StarAddMonoid A]
    {n m : ℕ} (h : n ≤ m) (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin m) :
    zeroExtendStarAlgHom h X i j =
      if hi : i.val < n then
        if hj : j.val < n then X ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else 0 :=
  rfl

/-- Let `A` be a possibly nonunital ring. `A` has a complex module structure. `A` has an additive star
involution. For natural numbers `n` and `m`. Assume `n ≤ m`. Finite zero padding is injective
through the retained entries, with no norm or nonzero-coefficient hypothesis.
-/
theorem zeroExtendStarAlgHom_injective
    {A : Type u} [NonUnitalRing A] [Module ℂ A] [StarAddMonoid A]
    {n m : ℕ} (h : n ≤ m) :
    Function.Injective (zeroExtendStarAlgHom (A := A) h) := by
  intro X Y hXY
  apply (ofMatrix (m := Fin n) (n := Fin n) (A := A)).symm.injective
  apply Matrix.zeroExtend_injective h
  have hCopy :=
    congrArg (ofMatrix (m := Fin m) (n := Fin m) (A := A)).symm hXY
  change Matrix.zeroExtend h (ofMatrix.symm X) =
    Matrix.zeroExtend h (ofMatrix.symm Y) at hCopy
  exact hCopy

/-- Let `A` be a possibly nonunital complex C*-algebra. For natural numbers `n` and `m`. Assume `n ≤ m`.
Use the spectral order on `A`. Finite square padding preserves the operator metric for complete
nonunital C-star coefficients, under their computed spectral order.
-/
theorem zeroExtendStarAlgHom_isometry
    {A : Type u} [NonUnitalCStarAlgebra A]
    {n m : ℕ} (h : n ≤ m) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A;
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A;
    Isometry (zeroExtendStarAlgHom (A := A) h :
      CStarMatrix (Fin n) (Fin n) A → CStarMatrix (Fin m) (Fin m) A) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact NonUnitalStarAlgHom.isometry (zeroExtendStarAlgHom (A := A) h)
    (zeroExtendStarAlgHom_injective (A := A) h)

end CStarMatrix
