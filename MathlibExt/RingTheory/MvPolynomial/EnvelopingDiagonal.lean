/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Original polynomial enveloping factors and actual diagonal coordinates. -/
module

public import MathlibExt.RingTheory.MvPolynomial.Translation
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.Algebra.Opposite

/-!
# The polynomial diagonal in its actual enveloping algebra

The original algebra is `MvPolynomial σ k`; the original enveloping algebra
retains its opposite right factor. Native opposite, tensor and sum-variable
equivalences identify it with the actual two-copy polynomial algebra.
Translation then makes `X_left - X_right` the outer polynomial variables,
while the original right variables remain the coefficient algebra.

The multiplication augmentation is the native tensor multiplication. Its
equality with evaluation of these new variables at zero is proved on the
original generators, rather than supplied as coordinate data.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v

namespace MvPolynomial

variable (k : Type u) [CommRing k] (σ : Type v)

/-- The original polynomial enveloping algebra, with its original opposite factor. -/
abbrev PolynomialEnveloping : Type (max u v) :=
  (MvPolynomial σ k) ⊗[k] (MvPolynomial σ k)ᵐᵒᵖ

/-- The original right-variable algebra remains the coefficient ring. -/
abbrev DiagonalPolynomial : Type (max u v) :=
  MvPolynomial σ (MvPolynomial σ k)

/-- Use the native commutative opposite equivalence without changing either tensor carrier. -/
def envelopingPlainEquiv :
    PolynomialEnveloping k σ ≃ₐ[k] (MvPolynomial σ k) ⊗[k] (MvPolynomial σ k) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (AlgEquiv.toOpposite k (MvPolynomial σ k)).symm

/-- The actual right opposite coordinate is unop, with the original order retained. -/
@[simp]
theorem envelopingPlainEquiv_tmul (a b : MvPolynomial σ k) :
    envelopingPlainEquiv k σ (a ⊗ₜ[k] MulOpposite.op b) = a ⊗ₜ[k] b := by
  simp only [envelopingPlainEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- The two actual polynomial factors are the two copies of the original variable type. -/
def envelopingEquivSum :
    PolynomialEnveloping k σ ≃ₐ[k] MvPolynomial (σ ⊕ σ) k :=
  (envelopingPlainEquiv k σ).trans (tensorEquivSum k σ σ k)

/-- The first original polynomial variable is the left sum variable. -/
@[simp]
theorem envelopingEquivSum_left_X (i : σ) :
    envelopingEquivSum k σ
        ((X i : MvPolynomial σ k) ⊗ₜ[k] (1 : (MvPolynomial σ k)ᵐᵒᵖ)) =
      X (Sum.inl i) := by
  have hv := envelopingPlainEquiv_tmul k σ (X i) (1 : MvPolynomial σ k)
  rw [MulOpposite.op_one] at hv
  change tensorEquivSum k σ σ k
    (envelopingPlainEquiv k σ
      ((X i : MvPolynomial σ k) ⊗ₜ[k] (1 : (MvPolynomial σ k)ᵐᵒᵖ))) = _
  calc
    _ = tensorEquivSum k σ σ k ((X i : MvPolynomial σ k) ⊗ₜ[k] 1) :=
      congrArg (tensorEquivSum k σ σ k) hv
    _ = X (Sum.inl i) := tensorEquivSum_X_tmul_one i

/-- The second original polynomial variable is the right sum variable. -/
@[simp]
theorem envelopingEquivSum_right_X (i : σ) :
    envelopingEquivSum k σ
        ((1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k)) =
      X (Sum.inr i) := by
  simp only [envelopingEquivSum, AlgEquiv.trans_apply, envelopingPlainEquiv_tmul,
    tensorEquivSum_one_tmul_X]

/-- The actual coordinate change makes left-minus-right the outer variables. -/
def envelopingDiagonalCoordinates :
    PolynomialEnveloping k σ ≃ₐ[k] DiagonalPolynomial k σ :=
  ((envelopingEquivSum k σ).trans (sumAlgEquiv k σ σ)).trans
    ((translationAlgEquiv (MvPolynomial σ k) (fun i : σ => X i)).restrictScalars k)

/-- The original left variable is difference plus the original right variable. -/
@[simp]
theorem envelopingDiagonalCoordinates_left_X (i : σ) :
    envelopingDiagonalCoordinates k σ
        ((X i : MvPolynomial σ k) ⊗ₜ[k] (1 : (MvPolynomial σ k)ᵐᵒᵖ)) =
      X i + C (X i : MvPolynomial σ k) := by
  change translationAlgEquiv (MvPolynomial σ k) (fun j : σ => X j)
    (sumAlgEquiv k σ σ
      (envelopingEquivSum k σ
        ((X i : MvPolynomial σ k) ⊗ₜ[k] (1 : (MvPolynomial σ k)ᵐᵒᵖ)))) = _
  rw [envelopingEquivSum_left_X, sumAlgEquiv_X_inl, translationAlgEquiv_X]

/-- The original right variable is a coefficient, without a new variable model. -/
@[simp]
theorem envelopingDiagonalCoordinates_right_X (i : σ) :
    envelopingDiagonalCoordinates k σ
        ((1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k)) =
      C (X i : MvPolynomial σ k) := by
  change translationAlgEquiv (MvPolynomial σ k) (fun j : σ => X j)
    (sumAlgEquiv k σ σ
      (envelopingEquivSum k σ
        ((1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k)))) = _
  rw [envelopingEquivSum_right_X, sumAlgEquiv_X_inr, translationAlgEquiv_C]

/-- The original left-minus-right diagonal relation in the original enveloping carrier. -/
def diagonalDifference (i : σ) : PolynomialEnveloping k σ :=
  (X i : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (1 : MvPolynomial σ k) -
    (1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k)

/-- Each original diagonal relation is the actual outer variable under the earned coordinates. -/
@[simp]
theorem envelopingDiagonalCoordinates_difference (i : σ) :
    envelopingDiagonalCoordinates k σ (diagonalDifference k σ i) = X i := by
  rw [diagonalDifference, map_sub, MulOpposite.op_one, envelopingDiagonalCoordinates_left_X,
    envelopingDiagonalCoordinates_right_X, add_sub_cancel_right]

/-- The inverse sends an outer variable to the original diagonal difference. -/
@[simp]
theorem envelopingDiagonalCoordinates_symm_X (i : σ) :
    (envelopingDiagonalCoordinates k σ).symm (X i) = diagonalDifference k σ i := by
  apply (envelopingDiagonalCoordinates k σ).injective
  rw [AlgEquiv.apply_symm_apply, envelopingDiagonalCoordinates_difference]

/-- The original polynomial multiplication augmentation. -/
def diagonalMultiplication : PolynomialEnveloping k σ →ₐ[k] MvPolynomial σ k :=
  (Algebra.TensorProduct.lmul' k).comp (envelopingPlainEquiv k σ).toAlgHom

/-- Multiplication retains both original polynomial factors in their original order. -/
@[simp]
theorem diagonalMultiplication_tmul (a b : MvPolynomial σ k) :
    diagonalMultiplication k σ (a ⊗ₜ[k] MulOpposite.op b) = a * b := by
  change (Algebra.TensorProduct.lmul' k)
    (envelopingPlainEquiv k σ (a ⊗ₜ[k] MulOpposite.op b)) = a * b
  rw [envelopingPlainEquiv_tmul, Algebra.TensorProduct.lmul'_apply_tmul]

/-- The actual multiplication augmentation kills each original diagonal difference. -/
@[simp]
theorem diagonalMultiplication_difference (i : σ) :
    diagonalMultiplication k σ (diagonalDifference k σ i) = 0 := by
  simp only [diagonalDifference, map_sub, diagonalMultiplication_tmul,
    mul_one, one_mul, sub_self]

/-- The actual multiplication is surjective by its original unit section. -/
theorem diagonalMultiplication_surjective : Function.Surjective (diagonalMultiplication k σ) := by
  intro a
  exact ⟨a ⊗ₜ[k] MulOpposite.op (1 : MvPolynomial σ k), by
    rw [diagonalMultiplication_tmul, mul_one]⟩

/-- Set the actual difference variables to zero, retaining the original right-variable algebra. -/
def diagonalEvalZero : DiagonalPolynomial k σ →ₐ[MvPolynomial σ k] MvPolynomial σ k :=
  aeval (fun _ : σ => (0 : MvPolynomial σ k))

/-- The earned coordinate augmentation is the original multiplication map. -/
theorem diagonalEvalZero_comp_coordinates :
    ((diagonalEvalZero k σ).restrictScalars k).comp
        (envelopingDiagonalCoordinates k σ).toAlgHom = diagonalMultiplication k σ := by
  let A := MvPolynomial σ k
  let E := PolynomialEnveloping k σ
  let f : E →ₐ[k] A := ((diagonalEvalZero k σ).restrictScalars k).comp
    (envelopingDiagonalCoordinates k σ).toAlgHom
  let g : E →ₐ[k] A := diagonalMultiplication k σ
  let L : A →ₐ[k] E := Algebra.TensorProduct.includeLeft
  let O : Aᵐᵒᵖ →ₐ[k] E := Algebra.TensorProduct.includeRight
  let e : A ≃ₐ[k] Aᵐᵒᵖ := AlgEquiv.toOpposite k A
  have hL : f.comp L = g.comp L := by
    apply MvPolynomial.algHom_ext
    intro i
    change diagonalEvalZero k σ
        (envelopingDiagonalCoordinates k σ
          ((X i : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (1 : MvPolynomial σ k))) =
      diagonalMultiplication k σ
        ((X i : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (1 : MvPolynomial σ k))
    erw [envelopingDiagonalCoordinates_left_X, diagonalMultiplication_tmul]
    simp [diagonalEvalZero, aeval_C]
  have hO : f.comp (O.comp e.toAlgHom) = g.comp (O.comp e.toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro i
    change diagonalEvalZero k σ
        (envelopingDiagonalCoordinates k σ
          ((1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k))) =
      diagonalMultiplication k σ
        ((1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k))
    simp [diagonalEvalZero, aeval_C]
  apply Algebra.TensorProduct.ext hL
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  exact DFunLike.congr_fun hO a

end MvPolynomial
