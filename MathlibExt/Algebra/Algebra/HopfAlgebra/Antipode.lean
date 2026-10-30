/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_antipode_antipode.lean`,
`P2M/Sol/S_HopfAlgebra_antipode_antipode.lean`,
`Theorems/Thm_HopfAlgebra_isUnit_withConv_algHom.lean`,
`P2M/Sol/S_HopfAlgebra_isUnit_withConv_algHom.lean`,
`Theorems/Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one.lean`,
`P2M/Sol/S_HopfAlgebra_exists_comp_antipode_convMul_eq_one.lean`,
`Theorems/Thm_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one.lean` and
`P2M/Sol/S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one.lean`
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
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Antipode involution and convolution inverses in Hopf algebras

The antipode of a commutative Hopf algebra is an involution and an algebra
homomorphism; algebra homomorphisms out of a Hopf algebra are convolution
units with inverse given by precomposition with the antipode; and a
convolution power is trivial on all points iff it is trivial on the
universal point.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace HopfAntipodeAux

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]

private theorem antipode_algebraMap (r : R) :
    HopfAlgebra.antipode R (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]

private theorem toConv_antipode_mul_toConv_id :
    WithConv.toConv (HopfAlgebra.antipode R (A := A)) *
        WithConv.toConv (LinearMap.id : A →ₗ[R] A)
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_coe, id_eq]
  exact HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (Coalgebra.Repr.arbitrary R a)

end HopfAntipodeAux

namespace HopfAntipodeAux

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]

private theorem sum_antipode_antipode_mul_antipode {a : A} {ι𝓡 : Type*}
    (𝓡 : Coalgebra.Repr R a ι𝓡) :
    ∑ i ∈ 𝓡.index, HopfAlgebra.antipode R (HopfAlgebra.antipode R (𝓡.left i)) *
        HopfAlgebra.antipode R (𝓡.right i)
      = algebraMap R A (Coalgebra.counit (R := R) a) := by
  calc ∑ i ∈ 𝓡.index, HopfAlgebra.antipode R (HopfAlgebra.antipode R (𝓡.left i)) *
          HopfAlgebra.antipode R (𝓡.right i)
      = ∑ i ∈ 𝓡.index, HopfAlgebra.antipode R
          (HopfAlgebra.antipode R (𝓡.left i) * 𝓡.right i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [HopfAlgebra.antipode_mul_antidistrib]
        exact mul_comm _ _
    _ = HopfAlgebra.antipode R
          (∑ i ∈ 𝓡.index, HopfAlgebra.antipode R (𝓡.left i) * 𝓡.right i) := by
        rw [map_sum]
    _ = HopfAlgebra.antipode R (algebraMap R A (Coalgebra.counit (R := R) a)) := by
        rw [HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit 𝓡]
    _ = algebraMap R A (Coalgebra.counit (R := R) a) := antipode_algebraMap _

private theorem toConv_antipode_comp_antipode_mul_toConv_antipode :
    WithConv.toConv (HopfAlgebra.antipode R ∘ₗ HopfAlgebra.antipode R : A →ₗ[R] A)
        * WithConv.toConv (HopfAlgebra.antipode R (A := A))
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
  exact sum_antipode_antipode_mul_antipode (Coalgebra.Repr.arbitrary R a)

private theorem antipode_comp_antipode :
    (HopfAlgebra.antipode R ∘ₗ HopfAlgebra.antipode R : A →ₗ[R] A) = LinearMap.id :=
  WithConv.toConv_injective
    (left_inv_eq_right_inv toConv_antipode_comp_antipode_mul_toConv_antipode
      toConv_antipode_mul_toConv_id)

end HopfAntipodeAux

/-- The antipode of a commutative Hopf algebra is an involution. -/
theorem HopfAlgebra.antipode_antipode {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A] (a : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (HopfAntipodeAux.antipode_comp_antipode (R := R) (A := A)) a

namespace HopfAntipodeAux

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]
variable {L : Type*} [CommSemiring L] [Algebra R L]

private theorem convMul_comp_antipode_right (φ : A →ₐ[R] L) :
    WithConv.toConv φ * WithConv.toConv (φ.comp (HopfAlgebra.antipodeAlgHom R A)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun a => ?_)
  simp only [AlgHom.convMul_def, AlgHom.convOne_def, WithConv.ofConv_toConv,
    AlgHom.coe_comp, Function.comp_apply,
    Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  calc ∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
          φ ((Coalgebra.Repr.arbitrary R a).left i) *
            φ (HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).right i))
      = φ (∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
          (Coalgebra.Repr.arbitrary R a).left i *
            HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).right i)) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun i _ => (φ.map_mul _ _).symm
    _ = φ (algebraMap R A (Coalgebra.counit (R := R) a)) := by
        rw [HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (Coalgebra.Repr.arbitrary R a)]
    _ = algebraMap R L (Coalgebra.counit (R := R) a) := φ.commutes _

private theorem convMul_comp_antipode_left (φ : A →ₐ[R] L) :
    WithConv.toConv (φ.comp (HopfAlgebra.antipodeAlgHom R A)) * WithConv.toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun a => ?_)
  simp only [AlgHom.convMul_def, AlgHom.convOne_def, WithConv.ofConv_toConv,
    AlgHom.coe_comp, Function.comp_apply,
    Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  rw [← (Coalgebra.Repr.arbitrary R a).eq]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  calc ∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
          φ (HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).left i)) *
            φ ((Coalgebra.Repr.arbitrary R a).right i)
      = φ (∑ i ∈ (Coalgebra.Repr.arbitrary R a).index,
          HopfAlgebra.antipode R ((Coalgebra.Repr.arbitrary R a).left i) *
            (Coalgebra.Repr.arbitrary R a).right i) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun i _ => (φ.map_mul _ _).symm
    _ = φ (algebraMap R A (Coalgebra.counit (R := R) a)) := by
        rw [HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (Coalgebra.Repr.arbitrary R a)]
    _ = algebraMap R L (Coalgebra.counit (R := R) a) := φ.commutes _

end HopfAntipodeAux

/-- Algebra homomorphisms out of a Hopf algebra are convolution units. -/
theorem HopfAlgebra.isUnit_withConv_algHom {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A]
    {L : Type*} [CommSemiring L] [Algebra R L]
    (φ : WithConv (A →ₐ[R] L)) : IsUnit φ := by
  refine ⟨⟨φ, WithConv.toConv ((WithConv.ofConv φ).comp (HopfAlgebra.antipodeAlgHom R A)), ?_, ?_⟩,
    rfl⟩
  · have h := HopfAntipodeAux.convMul_comp_antipode_right (R := R)
      (WithConv.ofConv φ)
    rwa [WithConv.toConv_ofConv] at h
  · have h := HopfAntipodeAux.convMul_comp_antipode_left (R := R) (WithConv.ofConv φ)
    rwa [WithConv.toConv_ofConv] at h

/-- Every algebra homomorphism out of a Hopf algebra has a convolution
inverse given by precomposition with the antipode. -/
theorem HopfAlgebra.exists_comp_antipode_convMul_eq_one
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : A →ₐ[K] L) :
    ∃ ν' : A →ₐ[K] L,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) ∧
      WithConv.toConv ν' * WithConv.toConv ν = 1 ∧
      WithConv.toConv ν * WithConv.toConv ν' = 1 := by
  refine ⟨ν.comp (HopfAlgebra.antipodeAlgHom K A), ?_, ?_, ?_⟩
  · ext a; rfl
  · apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (WithConv.toConv (ν.comp (HopfAlgebra.antipodeAlgHom K A)) *
      WithConv.toConv ν).ofConv a = (1 : WithConv (A →ₐ[K] L)).ofConv a
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift (ν.comp (HopfAlgebra.antipodeAlgHom K A))
          ν (fun _ _ => Commute.all _ _)).toLinearMap =
        ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ
          (HopfAlgebraStruct.antipode (R := K)).rTensor A := by
      apply TensorProduct.ext'
      intro x y
      simp [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul,
        HopfAlgebra.antipodeAlgHom_apply]
    have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
    change Algebra.TensorProduct.lift (ν.comp (HopfAlgebra.antipodeAlgHom K A))
      ν _ (Coalgebra.comul (R := K) a) = _
    rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
  · apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (WithConv.toConv ν *
      WithConv.toConv (ν.comp (HopfAlgebra.antipodeAlgHom K A))).ofConv a =
      (1 : WithConv (A →ₐ[K] L)).ofConv a
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift ν (ν.comp (HopfAlgebra.antipodeAlgHom K A))
          (fun _ _ => Commute.all _ _)).toLinearMap =
        ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ
          (HopfAlgebraStruct.antipode (R := K)).lTensor A := by
      apply TensorProduct.ext'
      intro x y
      simp [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        HopfAlgebra.antipodeAlgHom_apply]
    have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
    change Algebra.TensorProduct.lift ν (ν.comp (HopfAlgebra.antipodeAlgHom K A))
      _ (Coalgebra.comul (R := K) a) = _
    rw [h, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

namespace HopfAntipodeAux

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

private theorem lmul'_comp_map_comp {T : Type w} [CommRing T] [Algebra R T]
    (g : H →ₐ[R] T) (a b : H →ₐ[R] H) :
    (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map (g.comp a) (g.comp b)) =
      g.comp ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map a b)) := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.lmul'_apply_tmul]

private theorem toConv_comp_pow {T : Type w} [CommRing T] [Algebra R T]
    (g : H →ₐ[R] T) (u : WithConv (H →ₐ[R] H)) (k : ℕ) :
    (WithConv.toConv (g.comp u.ofConv)) ^ k = WithConv.toConv (g.comp (u ^ k).ofConv) := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_def, AlgHom.convOne_def]
      congr 1
      change (Algebra.ofId R T).comp (Bialgebra.counitAlgHom R H) =
        g.comp ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
      rw [← AlgHom.comp_assoc]
      congr 1
      exact (AlgHom.ext fun r => (g.commutes r).symm)
  | succ k ih =>
      rw [pow_succ, pow_succ, ih, AlgHom.convMul_def, AlgHom.convMul_def]
      congr 1
      change (Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (g.comp (u ^ k).ofConv) (g.comp u.ofConv)).comp
            (Bialgebra.comulAlgHom R H)) =
        g.comp ((Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (u ^ k).ofConv u.ofConv).comp (Bialgebra.comulAlgHom R H)))
      rw [← AlgHom.comp_assoc, lmul'_comp_map_comp, AlgHom.comp_assoc, AlgHom.comp_assoc]

end HopfAntipodeAux

/-- A convolution power is trivial on all points iff it is trivial on the
universal point. -/
theorem HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ) :
    (∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ m = 1) ↔
      (WithConv.toConv (AlgHom.id R H)) ^ m = 1 := by
  constructor
  · intro h
    exact h H (WithConv.toConv (AlgHom.id R H))
  · intro hid T _ _ f
    have hf : f = WithConv.toConv (f.ofConv.comp (WithConv.toConv (AlgHom.id R H)).ofConv) := by
      change f = WithConv.toConv (f.ofConv.comp (AlgHom.id R H))
      rw [AlgHom.comp_id]
    rw [hf, HopfAntipodeAux.toConv_comp_pow, hid]
    have h0 := HopfAntipodeAux.toConv_comp_pow f.ofConv (WithConv.toConv (AlgHom.id R H)) 0
    rw [pow_zero, pow_zero] at h0
    exact h0.symm
