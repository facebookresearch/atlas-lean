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
# Coordinates on the polynomial diagonal

For a commutative ring `k` and a type `σ`, put `A = k[σ]` and `E = A ⊗[k] Aᵐᵒᵖ`. The two
tensor copies identify with the variables of `k[σ ⊕ σ]`.

In diagonal coordinates `D = A[U_i]`, the right tensor variables are coefficients and the left
tensor variables become `U_i + C(X_i)`. Hence `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)` maps to `U_i`.
The coordinate change is a `k`-algebra equivalence `E ≃ₐ[k] D`.

Diagonal multiplication `µ(a ⊗ op(b)) = a*b` is surjective and kills `δ_i`. Under the
coordinate equivalence, it is evaluation at `U_i = 0`, fixing the coefficient algebra `A`.

References: Loday, *Cyclic Homology*, Sections 1.1 and 3.2.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v

namespace MvPolynomial

variable (k : Type u) [CommRing k] (σ : Type v)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. `PolynomialEnveloping k σ` is the enveloping `k`-algebra `E`, with the second tensor
factor carrying the opposite multiplication. -/
abbrev PolynomialEnveloping : Type (max u v) :=
  (MvPolynomial σ k) ⊗[k] (MvPolynomial σ k)ᵐᵒᵖ

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. `DiagonalPolynomial k σ = MvPolynomial σ A` is the polynomial algebra over the
coefficient copy `A`; its outer variables index the left-minus-right diagonal differences. -/
abbrev DiagonalPolynomial : Type (max u v) :=
  MvPolynomial σ (MvPolynomial σ k)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Commutativity of `A` gives the `k`-algebra equivalence `E ≃ₐ[k] A ⊗[k] A`, with `a ⊗
op(b) ↦ a ⊗ b`. Its inverse restores `op` in the second factor. -/
def envelopingPlainEquiv :
    PolynomialEnveloping k σ ≃ₐ[k] (MvPolynomial σ k) ⊗[k] (MvPolynomial σ k) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (AlgEquiv.toOpposite k (MvPolynomial σ k)).symm

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `a,b : A`, `envelopingPlainEquiv k σ (a ⊗ op(b)) = a ⊗ b` in `A ⊗[k] A`. -/
@[simp]
theorem envelopingPlainEquiv_tmul (a b : MvPolynomial σ k) :
    envelopingPlainEquiv k σ (a ⊗ₜ[k] MulOpposite.op b) = a ⊗ₜ[k] b := by
  simp only [envelopingPlainEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. This is the `k`-algebra equivalence `E ≃ₐ[k] MvPolynomial (σ ⊕ σ) k`. A left tensor
variable maps to `X_(Sum.inl i)` and a right tensor variable maps to `X_(Sum.inr i)`. -/
def envelopingEquivSum :
    PolynomialEnveloping k σ ≃ₐ[k] MvPolynomial (σ ⊕ σ) k :=
  (envelopingPlainEquiv k σ).trans (tensorEquivSum k σ σ k)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `i : σ`, `envelopingEquivSum k σ (X_i ⊗ 1) = X_(Sum.inl i)` in `MvPolynomial (σ ⊕
σ) k`. -/
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

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `i : σ`, `envelopingEquivSum k σ (1 ⊗ op(X_i)) = X_(Sum.inr i)` in `MvPolynomial (σ
⊕ σ) k`. -/
@[simp]
theorem envelopingEquivSum_right_X (i : σ) :
    envelopingEquivSum k σ
        ((1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k)) =
      X (Sum.inr i) := by
  simp only [envelopingEquivSum, AlgEquiv.trans_apply, envelopingPlainEquiv_tmul,
    tensorEquivSum_one_tmul_X]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. The `k`-algebra equivalence `Ψ : E ≃ₐ[k] D` sends `X_i ⊗ 1` to `U_i + C(X_i)` and `1 ⊗
op(X_i)` to `C(X_i)`. Therefore `Ψ(δ_i) = U_i` for `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`. -/
def envelopingDiagonalCoordinates :
    PolynomialEnveloping k σ ≃ₐ[k] DiagonalPolynomial k σ :=
  ((envelopingEquivSum k σ).trans (sumAlgEquiv k σ σ)).trans
    ((translationAlgEquiv (MvPolynomial σ k) (fun i : σ => X i)).restrictScalars k)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. For `i : σ`, `envelopingDiagonalCoordinates k σ (X_i ⊗ 1) = U_i + C(X_i)`. -/
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

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. For `i : σ`, `envelopingDiagonalCoordinates k σ (1 ⊗ op(X_i)) = C(X_i)`, a coefficient
in `D`. -/
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

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `i : σ`, `diagonalDifference k σ i` is `X_i ⊗ op(1) - 1 ⊗ op(X_i)` in `E`, with the
left-minus-right sign convention. -/
def diagonalDifference (i : σ) : PolynomialEnveloping k σ :=
  (X i : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (1 : MvPolynomial σ k) -
    (1 : MvPolynomial σ k) ⊗ₜ[k] MulOpposite.op (X i : MvPolynomial σ k)

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. For every `i : σ`, the coordinate equivalence satisfies `envelopingDiagonalCoordinates k
σ (diagonalDifference k σ i) = U_i`. -/
@[simp]
theorem envelopingDiagonalCoordinates_difference (i : σ) :
    envelopingDiagonalCoordinates k σ (diagonalDifference k σ i) = X i := by
  rw [diagonalDifference, map_sub, MulOpposite.op_one, envelopingDiagonalCoordinates_left_X,
    envelopingDiagonalCoordinates_right_X, add_sub_cancel_right]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. For every `i : σ`, the inverse coordinate equivalence satisfies
`(envelopingDiagonalCoordinates k σ).symm U_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`. -/
@[simp]
theorem envelopingDiagonalCoordinates_symm_X (i : σ) :
    (envelopingDiagonalCoordinates k σ).symm (X i) = diagonalDifference k σ i := by
  apply (envelopingDiagonalCoordinates k σ).injective
  rw [AlgEquiv.apply_symm_apply, envelopingDiagonalCoordinates_difference]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. This is the `k`-algebra homomorphism `µ : E →ₐ[k] A` given on pure tensors by `µ(a ⊗
op(b)) = a*b`. -/
def diagonalMultiplication : PolynomialEnveloping k σ →ₐ[k] MvPolynomial σ k :=
  (Algebra.TensorProduct.lmul' k).comp (envelopingPlainEquiv k σ).toAlgHom

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For `a,b : A`, `diagonalMultiplication k σ (a ⊗ op(b)) = a*b`. -/
@[simp]
theorem diagonalMultiplication_tmul (a b : MvPolynomial σ k) :
    diagonalMultiplication k σ (a ⊗ₜ[k] MulOpposite.op b) = a * b := by
  change (Algebra.TensorProduct.lmul' k)
    (envelopingPlainEquiv k σ (a ⊗ₜ[k] MulOpposite.op b)) = a * b
  rw [envelopingPlainEquiv_tmul, Algebra.TensorProduct.lmul'_apply_tmul]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. For every `i : σ`, `diagonalMultiplication k σ (X_i ⊗ op(1) - 1 ⊗ op(X_i)) = 0`. -/
@[simp]
theorem diagonalMultiplication_difference (i : σ) :
    diagonalMultiplication k σ (diagonalDifference k σ i) = 0 := by
  simp only [diagonalDifference, map_sub, diagonalMultiplication_tmul,
    mul_one, one_mul, sub_self]

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. The map `diagonalMultiplication k σ : E → A` is surjective. Every `a : A` is the image
of `a ⊗ op(1)`. -/
theorem diagonalMultiplication_surjective : Function.Surjective (diagonalMultiplication k σ) := by
  intro a
  exact ⟨a ⊗ₜ[k] MulOpposite.op (1 : MvPolynomial σ k), by
    rw [diagonalMultiplication_tmul, mul_one]⟩

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. `diagonalEvalZero k σ : D →ₐ[A] A` fixes the coefficient algebra and sends every outer
variable `U_i` to zero. -/
def diagonalEvalZero : DiagonalPolynomial k σ →ₐ[MvPolynomial σ k] MvPolynomial σ k :=
  aeval (fun _ : σ => (0 : MvPolynomial σ k))

/-- Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Put `D = MvPolynomial σ A`, with outer variables `U_i` and coefficient embedding `C : A
→ D`. If `Ψ = envelopingDiagonalCoordinates k σ` and `ev₀ = diagonalEvalZero k σ`, then `ev₀ ∘
Ψ = diagonalMultiplication k σ` as `k`-algebra homomorphisms `E → A`. -/
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
