/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.ModuleFirstOrder
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.NormNum

/-!
# First-order multiplication for the polynomial ideal `(X)`

Let `R = ℤ[X]`, `I = (X)`, and take the flat regular module `R`.
The first-order multiplication equivalence sends `[1] ⊗ [X]` to `[X]`
and `[2] ⊗ [X]` to `[2X]` in `I/I²`. Both classes are nonzero, as
their coefficient of `X` is respectively one and two; elements of `(X²)`
have zero coefficient of `X`.

The inverse recovers the unit tensor, multiplication by `X` linearizes to
that tensor, and the next-order element `X²` has zero first-order class.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Pointwise

namespace FirstOrderPolynomialTests

abbrev R := Polynomial ℤ
abbrev X : R := Polynomial.X
abbrev I : Ideal R := Ideal.span {X}
abbrev IM : Submodule R R := I • ⊤
abbrev Reduced := R ⧸ IM
abbrev Source := Reduced ⊗[R ⧸ I] I.Cotangent

abbrev iX : I := ⟨X, Ideal.mem_span_singleton_self X⟩

abbrev xElement : IM :=
  ⟨X, by
    simpa only [smul_eq_mul, mul_one] using
      (Submodule.smul_mem_smul iX.property
        (Submodule.mem_top : (1 : R) ∈ (⊤ : Submodule R R)))⟩

abbrev twoXElement : IM := (2 : R) • xElement
abbrev xClass : I.FirstOrderModuleLayer R := Submodule.Quotient.mk xElement
abbrev twoXClass : I.FirstOrderModuleLayer R := Submodule.Quotient.mk twoXElement
abbrev squareClass : I.FirstOrderModuleLayer R := Submodule.Quotient.mk (X • xElement)

abbrev sourceOne : Source :=
  Submodule.Quotient.mk (1 : R) ⊗ₜ[R ⧸ I] I.toCotangent iX

abbrev sourceTwo : Source :=
  Submodule.Quotient.mk (2 : R) ⊗ₜ[R ⧸ I] I.toCotangent iX

abbrev sourceX : Source :=
  Submodule.Quotient.mk X ⊗ₜ[R ⧸ I] I.toCotangent iX

abbrev E : Source ≃ₗ[R ⧸ I] I.FirstOrderModuleLayer R := I.firstOrderMulEquiv R
abbrev multiplyX : R →ₗ[R] R := X • LinearMap.id

private lemma equivalence_value (t : Source) : E t = I.firstOrderMul R t :=
  (congrFun (LinearEquiv.coe_toLinearMap E) t).symm.trans
    (LinearMap.congr_fun (Ideal.firstOrderMulEquiv_toLinearMap I R) t)

private lemma one_value : E sourceOne = xClass := by
  calc
    _ = I.firstOrderMul R sourceOne := equivalence_value sourceOne
    _ = Submodule.Quotient.mk
        (⟨iX.val • (1 : R), Submodule.smul_mem_smul iX.property Submodule.mem_top⟩ : IM) :=
      Ideal.firstOrderMul_mk_tmul_toCotangent I R (1 : R) iX
    _ = xClass :=
      congrArg (fun z : IM => (Submodule.Quotient.mk z : I.FirstOrderModuleLayer R))
        (Subtype.ext (by simp only [iX, xElement, smul_eq_mul, mul_one]))

private lemma two_value : E sourceTwo = twoXClass := by
  calc
    _ = I.firstOrderMul R sourceTwo := equivalence_value sourceTwo
    _ = Submodule.Quotient.mk
        (⟨iX.val • (2 : R), Submodule.smul_mem_smul iX.property Submodule.mem_top⟩ : IM) :=
      Ideal.firstOrderMul_mk_tmul_toCotangent I R (2 : R) iX
    _ = twoXClass :=
      congrArg (fun z : IM => (Submodule.Quotient.mk z : I.FirstOrderModuleLayer R))
        (Subtype.ext (by
          change X * (2 : R) = (2 : R) * X
          exact mul_comm _ _))

private lemma coeff_one_of_mem_square (f : R) (hf : f ∈ I ^ 2) : f.coeff 1 = 0 := by
  have hspan : f ∈ (Ideal.span {X ^ 2} : Ideal R) := by
    simpa only [I, Ideal.span_singleton_pow] using hf
  have hdiv : X ^ 2 ∣ f := Ideal.mem_span_singleton.mp hspan
  exact (Polynomial.X_pow_dvd_iff.mp hdiv) 1 (by decide)

private lemma coeff_one_of_class_zero (z : IM)
    (hz : (Submodule.Quotient.mk z : I.FirstOrderModuleLayer R) = 0) : z.val.coeff 1 = 0 := by
  have hmem : z ∈ I • (⊤ : Submodule R IM) :=
    (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R IM))).mp hz
  have hm : (z : R) ∈ I • IM :=
    (Submodule.mem_smul_top_iff (I := I) IM z).mp hmem
  have hs : I • IM = (I ^ 2 : Submodule R R) := by
    change I • (I • (⊤ : Ideal R)) = I ^ 2
    rw [Ideal.smul_eq_mul, Ideal.smul_eq_mul, Ideal.mul_top, pow_two]
  exact coeff_one_of_mem_square z.val (hs ▸ hm)

private lemma x_class_ne_zero : xClass ≠ 0 := by
  intro h
  have hc := coeff_one_of_class_zero xElement h
  have hOne : (1 : ℤ) = 0 := by simpa [xElement, X] using hc
  exact one_ne_zero hOne

private lemma two_x_class_ne_zero : twoXClass ≠ 0 := by
  intro h
  have hc := coeff_one_of_class_zero twoXElement h
  have hTwo : (2 : ℤ) = 0 := by
    simpa [twoXElement, xElement, smul_eq_mul, two_mul, X] using hc
  norm_num at hTwo

lemma range_multiplyX : LinearMap.range multiplyX ≤ IM := by
  rintro z ⟨r, rfl⟩
  change X • r ∈ I • (⊤ : Submodule R R)
  exact Submodule.smul_mem_smul iX.property Submodule.mem_top

/-- First-order multiplication sends `[1] ⊗ [X]` to `[X]` in `I/I²`. -/
example : E sourceOne = xClass := one_value

/-- The coefficient-two tensor is sent to the class of `2X`. -/
example : E sourceTwo = twoXClass := two_value

/-- The generator `X` has nonzero first-order class, detected by coefficient one. -/
example : xClass ≠ 0 := x_class_ne_zero

/-- The coefficient-two first-order class remains nonzero over the integers. -/
example : twoXClass ≠ 0 := two_x_class_ne_zero

/-- The tensor `[1] ⊗ [X]` is nonzero. -/
example : sourceOne ≠ 0 := by
  intro h
  have hx : xClass = 0 := one_value.symm.trans
    ((congrArg E h).trans (map_zero E))
  exact x_class_ne_zero hx

/-- The cotangent class of `X` is nonzero in `I/I²`. -/
example : I.toCotangent iX ≠ 0 := by
  intro h
  have hm : X ∈ I ^ 2 := (Ideal.toCotangent_eq_zero I iX).mp h
  have hc := coeff_one_of_mem_square X hm
  have hOne : (1 : ℤ) = 0 := by simpa [X] using hc
  exact one_ne_zero hOne

/-- The inverse first-order equivalence recovers `[1] ⊗ [X]` from the class of `X`. -/
example : E.symm xClass = sourceOne :=
  (congrArg E.symm one_value).symm.trans (E.symm_apply_apply sourceOne)

/-- A first coefficient in `(X)` gives zero after first-order multiplication. -/
example : E sourceX = 0 := by
  have hx : (Submodule.Quotient.mk X : Reduced) = 0 :=
    (Submodule.Quotient.mk_eq_zero IM).mpr xElement.property
  have ht : sourceX = 0 := by
    change (Submodule.Quotient.mk X : Reduced) ⊗ₜ[R ⧸ I] I.toCotangent iX = 0
    rw [hx, TensorProduct.zero_tmul]
  exact (congrArg E ht).trans (map_zero E)

/-- The next-order representative `X²` has zero first-order class. -/
example : squareClass = 0 := by
  change (Submodule.Quotient.mk (X • xElement) : I.FirstOrderModuleLayer R) = 0
  exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R IM))).mpr
    (Submodule.smul_mem_smul iX.property
      (Submodule.mem_top : xElement ∈ (⊤ : Submodule R IM)))

/-- Multiplication by `X` has tensor-valued first-order linearization `[1] ↦ [1] ⊗ [X]`. -/
example : multiplyX.linearizationAtIdeal I range_multiplyX
    (Submodule.Quotient.mk (1 : R)) = sourceOne := by
  apply E.injective
  calc
    _ = I.firstOrderMul R (multiplyX.linearizationAtIdeal I range_multiplyX
        (Submodule.Quotient.mk (1 : R))) := equivalence_value _
    _ = Submodule.Quotient.mk
        (⟨multiplyX 1, range_multiplyX (LinearMap.mem_range_self multiplyX 1)⟩ : IM) :=
      LinearMap.firstOrderMul_linearizationAtIdeal_mk I multiplyX range_multiplyX 1
    _ = xClass :=
      congrArg (fun z : IM => (Submodule.Quotient.mk z : I.FirstOrderModuleLayer R))
        (Subtype.ext (by
          change X * (1 : R) = X
          exact mul_one _))
    _ = _ := one_value.symm

end FirstOrderPolynomialTests
