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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaFinite
public import Mathlib.Data.Matrix.Basic

/-!
# Finite-frame examples

Finite frames are used with independent module universes and with the
regular matrix-ring Pair in sizes two and zero.
-/

@[expose] public section

noncomputable section

open MulOpposite TensorProduct.Balanced

universe r s p q

namespace TensorProduct.Balanced.Morita.PublicFiniteFrames

section Arbitrary

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P : Type p) (Q : Type q) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (u : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced ℤ S P Q), u (r • b) = r * u b)
  (w : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced ℤ R Q P), w (s • b) = s * w b)

include u in
example : u.symm 1 = ∑ i ∈ unitSupport R S P Q u, mk ℤ S P Q i.1 i.2 :=
  unitSupport_eq R S P Q u

include u in
example : u (∑ i ∈ unitSupport R S P Q u, mk ℤ S P Q i.1 i.2) = 1 :=
  unitSupport_sum R S P Q u

include u hu w hw in
example : Module.Finite R P ∧ Module.Projective R P :=
  p_left_finite_projective R S P Q u hu w hw

include u hu w hw in
example : Module.Finite Sᵐᵒᵖ P ∧ Module.Projective Sᵐᵒᵖ P :=
  p_right_finite_projective R S P Q u hu w hw

include u hu w hw in
example : Module.Finite S Q ∧ Module.Projective S Q :=
  q_left_finite_projective R S P Q u hu w hw

include u hu w hw in
example : Module.Finite Rᵐᵒᵖ Q ∧ Module.Projective Rᵐᵒᵖ Q :=
  q_right_finite_projective R S P Q u hu w hw

end Arbitrary

section RegularRing

variable (A : Type r) [Ring A]

/-- The native regular-factor unitor, with its earned right A linearity. -/
def selfContraction :
    letI := leftModule ℤ A A A A
    letI := rightModule ℤ A A A A
    TensorProduct.Balanced ℤ A A A ≃ₗ[Aᵐᵒᵖ] A := by
  letI := leftModule ℤ A A A A
  letI := rightModule ℤ A A A A
  let e := leftUnitor ℤ A A
  refine e.toAddEquiv.toLinearEquiv (fun t x => ?_)
  have h : e.toLinearMap.toAddMonoidHom.comp
      (DistribSMul.toAddMonoidHom (TensorProduct.Balanced ℤ A A A) t) =
      (DistribSMul.toAddMonoidHom A t).comp e.toLinearMap.toAddMonoidHom := by
    apply addHom_ext ℤ A A A
    intro a b
    change e (t • mk ℤ A A A a b) = t • e (mk ℤ A A A a b)
    rw [rightModule_smul_mk, leftUnitor_mk, leftUnitor_mk]
    change a * (b * t.unop) = (a * b) * t.unop
    exact (mul_assoc a b t.unop).symm
  exact DFunLike.congr_fun h x

/-- Its left A linearity follows from the native multiplication associativity. -/
theorem selfContraction_left (a : A) (b : TensorProduct.Balanced ℤ A A A) :
    letI := leftModule ℤ A A A A
    letI := rightModule ℤ A A A A
    selfContraction A (a • b) = a * selfContraction A b := by
  let := leftModule ℤ A A A A
  let := rightModule ℤ A A A A
  let e := leftUnitor ℤ A A
  have h : e.toLinearMap.toAddMonoidHom.comp
      (leftAction ℤ A A A A a).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom A a).comp e.toLinearMap.toAddMonoidHom := by
    apply addHom_ext ℤ A A A
    intro x y
    change e (leftAction ℤ A A A A a (mk ℤ A A A x y)) = a * e (mk ℤ A A A x y)
    rw [leftAction_mk, leftUnitor_mk, leftUnitor_mk]
    change (a * x) * y = a * (x * y)
    exact mul_assoc a x y
  exact DFunLike.congr_fun h b

end RegularRing

/-- A genuine noncommutative ring used by the finite-frame formula. -/
abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

example (a : MatrixRing) :
    ∑ i : unitSupport MatrixRing MatrixRing MatrixRing MatrixRing (selfContraction MatrixRing),
      leftCoefficient MatrixRing MatrixRing MatrixRing MatrixRing
        (normalizedContraction MatrixRing MatrixRing MatrixRing MatrixRing
          (selfContraction MatrixRing) (selfContraction MatrixRing)
          (selfContraction_left MatrixRing))
        (normalizedContraction_left MatrixRing MatrixRing MatrixRing MatrixRing
          (selfContraction MatrixRing) (selfContraction_left MatrixRing)
          (selfContraction MatrixRing) (selfContraction_left MatrixRing)) i.1.1 a • i.1.2 = a :=
  p_left_frame MatrixRing MatrixRing MatrixRing MatrixRing
    (selfContraction MatrixRing) (selfContraction_left MatrixRing)
    (selfContraction MatrixRing) (selfContraction_left MatrixRing) a

/-- The zero-size regular matrix ring requires no Nontrivial or positive-cardinality premise. -/
abbrev ZeroMatrixRing := Matrix (Fin 0) (Fin 0) ℤ

example : Module.Finite ZeroMatrixRingᵐᵒᵖ ZeroMatrixRing ∧
    Module.Projective ZeroMatrixRingᵐᵒᵖ ZeroMatrixRing :=
  p_right_finite_projective ZeroMatrixRing ZeroMatrixRing ZeroMatrixRing ZeroMatrixRing
    (selfContraction ZeroMatrixRing) (selfContraction_left ZeroMatrixRing)
    (selfContraction ZeroMatrixRing) (selfContraction_left ZeroMatrixRing)

end TensorProduct.Balanced.Morita.PublicFiniteFrames
