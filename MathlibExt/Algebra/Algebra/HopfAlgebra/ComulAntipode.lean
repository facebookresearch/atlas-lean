/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_comul_antipode.lean`,
`P2M/Sol/S_HopfAlgebra_comul_antipode.lean`,
`Theorems/Thm_HopfAlgebra_map_antipode_comul_of_isCocomm.lean` and
`P2M/Sol/S_HopfAlgebra_map_antipode_comul_of_isCocomm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Comultiplication of the antipode

Comultiplication anticommutes with the antipode up to the tensor swap;
in a cocommutative Hopf algebra the swap is trivial, so comultiplication
commutes with the antipode.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace HopfComulAntipodeAux

variable {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [HopfAlgebra R A]

private theorem toConv_includeLeft_comp_antipode_mul_toConv_includeLeft :
    WithConv.toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ
          HopfAlgebra.antipode R)
        * WithConv.toConv
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Algebra.TensorProduct.algebraMap_apply,
    ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (Coalgebra.Repr.arbitrary R a)]
  exact (TensorProduct.sum_tmul _ _ _).symm

private theorem toConv_includeRight_comp_antipode_mul_toConv_includeRight :
    WithConv.toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ
          HopfAlgebra.antipode R)
        * WithConv.toConv
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Algebra.TensorProduct.algebraMap_apply',
    ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (Coalgebra.Repr.arbitrary R a)]
  exact (TensorProduct.tmul_sum _ _ _).symm

private theorem toConv_includeLeft_mul_toConv_includeRight :
    WithConv.toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
        * WithConv.toConv (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
      = WithConv.toConv (Coalgebra.comul : A →ₗ[R] A ⊗[R] A) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, LinearMap.comp_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem toConv_includeRight_comp_antipode_mul_toConv_includeLeft_comp_antipode :
    WithConv.toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ
          HopfAlgebra.antipode R)
        * WithConv.toConv
          ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ
            HopfAlgebra.antipode R)
      = WithConv.toConv ((TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) ∘ₗ
            Coalgebra.comul) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, LinearMap.comp_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul, LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul]

private theorem toConv_comm_map_antipode_comul_mul_toConv_comul :
    WithConv.toConv ((TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) ∘ₗ
            Coalgebra.comul)
        * WithConv.toConv (Coalgebra.comul : A →ₗ[R] A ⊗[R] A)
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  rw [← toConv_includeRight_comp_antipode_mul_toConv_includeLeft_comp_antipode,
    ← toConv_includeLeft_mul_toConv_includeRight, mul_assoc,
    ← mul_assoc (WithConv.toConv
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ
        HopfAlgebra.antipode R)),
    toConv_includeLeft_comp_antipode_mul_toConv_includeLeft, one_mul]
  exact toConv_includeRight_comp_antipode_mul_toConv_includeRight

private theorem toConv_comul_mul_toConv_comul_comp_antipode :
    WithConv.toConv (Coalgebra.comul : A →ₗ[R] A ⊗[R] A)
        * WithConv.toConv (Coalgebra.comul ∘ₗ HopfAlgebra.antipode R :
          A →ₗ[R] A ⊗[R] A)
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    ← Bialgebra.comul_mul]
  rw [show ∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
        Coalgebra.comul (R := R) ((Coalgebra.Repr.arbitrary R a).left i *
          HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).right i))
      = Coalgebra.comul (R := R) (∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
        (Coalgebra.Repr.arbitrary R a).left i *
          HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).right i)) from
      (map_sum _ _ _).symm,
    HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (Coalgebra.Repr.arbitrary R a),
    Bialgebra.comul_algebraMap]

private theorem comul_comp_antipode :
    Coalgebra.comul ∘ₗ HopfAlgebra.antipode R
      = (TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) ∘ₗ
            Coalgebra.comul :=
  (WithConv.toConv_injective
    (left_inv_eq_right_inv
      (toConv_comm_map_antipode_comul_mul_toConv_comul (R := R) (A := A))
      (toConv_comul_mul_toConv_comul_comp_antipode (R := R) (A := A)))).symm

end HopfComulAntipodeAux

/-- Comultiplication anticommutes with the antipode up to the tensor swap. -/
theorem HopfAlgebra.comul_antipode {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (a : A) :
    Coalgebra.comul (HopfAlgebra.antipode R a)
      = TensorProduct.comm R A A
          (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)
            (Coalgebra.comul a)) := by
  have h := LinearMap.congr_fun
    (HopfComulAntipodeAux.comul_comp_antipode (R := R) (A := A)) a
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h

/-- In a cocommutative Hopf algebra, comultiplication commutes with the
antipode. -/
theorem HopfAlgebra.map_antipode_comul_of_isCocomm {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (hcocomm : Coalgebra.IsCocomm R A) (a : A) :
    TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) (Coalgebra.comul a)
      = Coalgebra.comul (HopfAlgebra.antipode R a) := by
  have _ := hcocomm
  have h := HopfAlgebra.comul_antipode (R := R) (A := A) a
  rw [h]
  have hτS : ∀ z : A ⊗[R] A,
      TensorProduct.comm R A A (TensorProduct.map (HopfAlgebra.antipode R)
        (HopfAlgebra.antipode R) z)
        = TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)
          (TensorProduct.comm R A A z) := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro x y
      simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
    · intro z₁ z₂ h₁ h₂
      simp [map_add, h₁, h₂]
  rw [hτS]
  congr 1
  exact (Coalgebra.comm_comul (R := R) a).symm
