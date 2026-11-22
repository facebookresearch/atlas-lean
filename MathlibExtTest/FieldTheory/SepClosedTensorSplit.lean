/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.SepClosedTensorSplit

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section

open scoped TensorProduct

/-- There is only one `ℚ`-algebra homomorphism `ℚ → ℂ`. -/
public theorem test_card_algHom_rat_complex : Fintype.card (ℚ →ₐ[ℚ] ℂ) = 1 := by
  rw [Algebra.TensorProduct.algHom_card_eq_finrank_of_isSepClosed]
  exact Module.finrank_self ℚ

/-- There are exactly two `ℝ`-algebra homomorphisms `ℂ → ℂ`. -/
public theorem test_card_algHom_complex_complex_real :
    Fintype.card (ℂ →ₐ[ℝ] ℂ) = 2 := by
  rw [Algebra.TensorProduct.algHom_card_eq_finrank_of_isSepClosed]
  exact Complex.finrank_real_complex

/-- The splitting isomorphism sends `1 ⊗ I` to the identity embedding at
the identity embedding. -/
public theorem test_sepClosedAlgEquiv_apply_I_id :
    Algebra.TensorProduct.sepClosedAlgEquiv ℝ ℂ ℂ (1 ⊗ₜ[ℝ] Complex.I)
      (AlgHom.id ℝ ℂ) = Complex.I := by
  rw [Algebra.TensorProduct.sepClosedAlgEquiv_apply]
  simp

/-- The splitting isomorphism sends `1 ⊗ I` to `-I` at complex conjugation. -/
public theorem test_sepClosedAlgEquiv_apply_I_conj :
    Algebra.TensorProduct.sepClosedAlgEquiv ℝ ℂ ℂ (1 ⊗ₜ[ℝ] Complex.I)
      Complex.conjAe.toAlgHom = -Complex.I := by
  rw [Algebra.TensorProduct.sepClosedAlgEquiv_apply]
  simp [Complex.conjAe]

/-- The splitting isomorphism sends `ω ⊗ 1` to the constant function `ω`. -/
public theorem test_sepClosedAlgEquiv_apply_tmul_one :
    Algebra.TensorProduct.sepClosedAlgEquiv ℝ ℂ ℂ (Complex.I ⊗ₜ[ℝ] (1 : ℝ))
      = fun _ => Complex.I := by
  rw [Algebra.TensorProduct.sepClosedAlgEquiv_apply]
  funext σ
  simp

/-- The splitting isomorphism is bijective. -/
public theorem test_sepClosedAlgEquiv_bijective :
    Function.Bijective (Algebra.TensorProduct.sepClosedAlgEquiv ℝ ℂ ℂ) :=
  (Algebra.TensorProduct.sepClosedAlgEquiv ℝ ℂ ℂ).bijective
