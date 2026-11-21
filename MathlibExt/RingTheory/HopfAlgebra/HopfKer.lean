/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_HopfAlgebra_HopfKer.lean`,
`Definitions/Def_HopfAlgebra_HopfKerHopf.lean` and
`Definitions/Def_HopfAlgebra_HopfIdealQuotient.lean`
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

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient

@[expose] public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing
  B] [Bialgebra R B]

noncomputable def coaction (π : A →ₐc[R] B) : A →ₐ[R] A ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)).comp (Bialgebra.comulAlgHom R A)

theorem coaction_apply (π : A →ₐc[R] B) (a : A) :
    coaction π a = Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) (Coalgebra.comul (R :=
      R) a) := rfl

noncomputable def hopfKer (π : A →ₐc[R] B) : Subalgebra R A :=
  AlgHom.equalizer (coaction π) (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)

theorem mem_hopfKer_iff (π : A →ₐc[R] B) (a : A) : a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R] 1 :=
  Iff.rfl

theorem coaction_eq_of_mem (π : A →ₐc[R] B) {a : A} (h : a ∈ hopfKer π) : coaction π a = a ⊗ₜ[R] 1
  := h

noncomputable def canAlgHom (π : A →ₐc[R] B) : A ⊗[R] A →ₐ[R] A ⊗[R] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) (coaction π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem canAlgHom_tmul (π : A →ₐc[R] B) (a a' : A) :
    canAlgHom π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  Algebra.TensorProduct.lift_tmul _ _ _ a a'

noncomputable def canMap (π : A →ₐc[R] B) : A ⊗[R] A →ₗ[R] A ⊗[R] B := (canAlgHom π).toLinearMap

theorem canMap_apply (π : A →ₐc[R] B) (z : A ⊗[R] A) : canMap π z = canAlgHom π z := rfl

@[simp] theorem canMap_tmul (π : A →ₐc[R] B) (a a' : A) :
    canMap π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  canAlgHom_tmul π a a'

theorem canMap_mul_tmul (π : A →ₐc[R] B) (a a' : A) {h : A} (hh : h ∈ hopfKer π) :
    canMap π ((a * h) ⊗ₜ[R] a') = canMap π (a ⊗ₜ[R] (h * a')) := by
  rw [canMap_tmul, canMap_tmul, map_mul, coaction_eq_of_mem π hh, ← mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]

theorem canMap_tmul_one (π : A →ₐc[R] B) (a : A) : canMap π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canMap_tmul, map_one, mul_one]

theorem canMap_one_tmul (π : A →ₐc[R] B) (a : A) : canMap π (1 ⊗ₜ[R] a) = coaction π a := by
  rw [canMap_tmul, ← Algebra.TensorProduct.one_def, one_mul]

def balancingRelations (π : A →ₐc[R] B) : Set (A ⊗[R] A) :=
  {x | ∃ (a h a' : A), h ∈ hopfKer π ∧ x = (a * h) ⊗ₜ[R] a' - a ⊗ₜ[R] (h * a')}

theorem canMap_eq_zero_of_mem_span (π : A →ₐc[R] B) {z : A ⊗[R] A}
    (hz : z ∈ Submodule.span R (balancingRelations π)) : canMap π z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, h, a', hh, rfl⟩ := hx
    rw [map_sub, canMap_mul_tmul π a a' hh, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

def IsHopfGalois (π : A →ₐc[R] B) : Prop :=
  Function.Surjective (canMap π) ∧ ∀ z, canMap π z = 0 → z ∈ Submodule.span R (balancingRelations π)

namespace HopfKerHopf

section AntiCoalgebra

open WithConv

noncomputable section

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [HopfAlgebra R A]

theorem toConv_includeLeft_comp_antipode_mul_toConv_includeLeft :
    toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
        * toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Algebra.TensorProduct.algebraMap_apply, ← sum_antipode_mul_eq_algebraMap_counit (ℛ R a)]
  exact (TensorProduct.sum_tmul _ _ _).symm

theorem toConv_includeRight_comp_antipode_mul_toConv_includeRight :
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
        * toConv (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Algebra.TensorProduct.algebraMap_apply', ← sum_antipode_mul_eq_algebraMap_counit (ℛ R a)]
  exact (TensorProduct.tmul_sum _ _ _).symm

theorem toConv_includeLeft_mul_toConv_includeRight :
    toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
        * toConv (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
      = toConv (comul : A →ₗ[R] A ⊗[R] A) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, LinearMap.comp_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem toConv_includeRight_comp_antipode_mul_toConv_includeLeft_comp_antipode :
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
        * toConv
            ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
      = toConv ((TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ comul) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, LinearMap.comp_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul, LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul]

theorem toConv_comm_map_antipode_comul_mul_toConv_comul :
    toConv ((TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ comul)
        * toConv (comul : A →ₗ[R] A ⊗[R] A)
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  rw [← toConv_includeRight_comp_antipode_mul_toConv_includeLeft_comp_antipode,
    ← toConv_includeLeft_mul_toConv_includeRight, mul_assoc,
    ← mul_assoc (toConv
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)),
    toConv_includeLeft_comp_antipode_mul_toConv_includeLeft, one_mul]
  exact toConv_includeRight_comp_antipode_mul_toConv_includeRight

theorem toConv_comul_mul_toConv_comul_comp_antipode :
    toConv (comul : A →ₗ[R] A ⊗[R] A)
        * toConv (comul ∘ₗ antipode R : A →ₗ[R] A ⊗[R] A)
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    ← Bialgebra.comul_mul]
  rw [show ∑ i ∈ (ℛ R a).index,
        comul (R := R) ((ℛ R a).left i * antipode R ((ℛ R a).right i))
      = comul (R := R) (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) from
      (map_sum _ _ _).symm,
    sum_mul_antipode_eq_algebraMap_counit (ℛ R a), Bialgebra.comul_algebraMap]

theorem comul_comp_antipode :
    comul ∘ₗ antipode R
      = (TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ comul :=
  (WithConv.toConv_injective
    (left_inv_eq_right_inv
      (toConv_comm_map_antipode_comul_mul_toConv_comul (R := R) (A := A))
      (toConv_comul_mul_toConv_comul_comp_antipode (R := R) (A := A)))).symm

theorem comul_antipode (a : A) :
    comul (antipode R a)
      = TensorProduct.comm R A A
          (TensorProduct.map (antipode R) (antipode R) (comul a)) := by
  have h := LinearMap.congr_fun (comul_comp_antipode (R := R) (A := A)) a
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h

theorem comul_antipode_eq_sum {a : A} {ι : Type*} (𝓡 : Coalgebra.Repr R a ι) :
    comul (antipode R a)
      = ∑ i ∈ 𝓡.index, antipode R (𝓡.right i) ⊗ₜ[R] antipode R (𝓡.left i) := by
  rw [comul_antipode a, ← 𝓡.eq]
  simp only [map_sum, TensorProduct.map_tmul, TensorProduct.comm_tmul]

end

end AntiCoalgebra

section MapAntipode

open WithConv

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B]

noncomputable def reprMap (π : A →ₐc[R] B) {a : A} {ι : Type*} (𝓡 : Coalgebra.Repr R a ι) :
    Coalgebra.Repr R (π a) ι where
  index := 𝓡.index
  left := fun i => π (𝓡.left i)
  right := fun i => π (𝓡.right i)
  eq := by
    rw [← CoalgHomClass.map_comp_comul_apply, ← 𝓡.eq, map_sum]
    simp only [TensorProduct.map_tmul]
    rfl

theorem map_antipode (π : A →ₐc[R] B) (a : A) : π (antipode R a) = antipode R (π a) := by

  let f : WithConv (A →ₗ[R] B) := toConv ((π : A →ₐc[R] B).toLinearMap ∘ₗ antipode R)
  let g : WithConv (A →ₗ[R] B) := toConv (antipode R ∘ₗ (π : A →ₐc[R] B).toLinearMap)
  let h : WithConv (A →ₗ[R] B) := toConv (π : A →ₐc[R] B).toLinearMap
  have hfh : f * h = 1 := by
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    rw [(ℛ R x).convMul_apply, LinearMap.convOne_def]
    simp only [f, h, WithConv.ofConv_toConv, LinearMap.comp_apply]
    have : ∑ i ∈ (ℛ R x).index, (π : A →ₐc[R] B).toLinearMap (antipode R ((ℛ R x).left i))
          * (π : A →ₐc[R] B).toLinearMap ((ℛ R x).right i)
        = π (∑ i ∈ (ℛ R x).index, antipode R ((ℛ R x).left i) * (ℛ R x).right i) := by
      rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; rfl
    rw [this, sum_antipode_mul_eq_algebraMap_counit, AlgHomClass.commutes]
    rfl
  have hhg : h * g = 1 := by
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    rw [(ℛ R x).convMul_apply, LinearMap.convOne_def]
    simp only [g, h, WithConv.ofConv_toConv, LinearMap.comp_apply]
    have := sum_mul_antipode_eq_algebraMap_counit (reprMap π (ℛ R x))
    simp only [reprMap] at this
    have e : ∀ i, (π : A →ₐc[R] B).toLinearMap ((ℛ R x).left i) * antipode R ((π : A →ₐc[R]
      B).toLinearMap ((ℛ R x).right i))
        = π ((ℛ R x).left i) * antipode R (π ((ℛ R x).right i)) := fun i => rfl
    simp only [e, this, CoalgHomClass.counit_comp_apply]
    rfl
  have := left_inv_eq_right_inv hfh hhg
  have := congr((WithConv.ofConv $this) a)
  simp only [f, g, WithConv.ofConv_toConv, LinearMap.comp_apply] at this
  exact this

end MapAntipode

section Stability

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)

theorem coaction_eq_map (a : A) :
    coaction π a
      = TensorProduct.map LinearMap.id (π : A →ₐc[R] B).toLinearMap (Coalgebra.comul (R := R) a) :=
        by
  rw [coaction_apply]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [Algebra.TensorProduct.map_tmul]; rfl

theorem coaction_repr {a : A} {ι : Type*} (𝓡 : Coalgebra.Repr R a ι) :
    coaction π a = ∑ i ∈ 𝓡.index, 𝓡.left i ⊗ₜ[R] π (𝓡.right i) := by
  rw [coaction_eq_map, ← 𝓡.eq, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem toLinearMap_apply' (x : A) : (π : A →ₐc[R] B).toLinearMap x = π x := rfl

theorem map_comm {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup
  Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (z : N ⊗[R]
      M) :
    TensorProduct.map f g (TensorProduct.comm R N M z) = TensorProduct.comm R Q P
      (TensorProduct.map g f z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem map_toLinearMap_id_comul [Coalgebra.IsCocomm R A] (x : A) :
    TensorProduct.map (π : A →ₐc[R] B).toLinearMap LinearMap.id (Coalgebra.comul (R := R) x)
      = TensorProduct.comm R A B (coaction π x) := by
  rw [coaction_eq_map, ← map_comm, Coalgebra.comm_comul]

theorem map_toLinearMap_id_comul' [Coalgebra.IsCocomm R A] (x : A) :
    TensorProduct.map (π : A →ₐc[R] B).toLinearMap LinearMap.id (Coalgebra.comul (R := R) x)
      = (TensorProduct.comm R A B).toLinearMap (coaction π x) :=
  map_toLinearMap_id_comul π x

theorem antipode_mem [Coalgebra.IsCocomm R A] {a : A} (ha : a ∈ hopfKer π) :
    antipode R a ∈ hopfKer π := by
  rw [mem_hopfKer_iff, coaction_eq_map, comul_antipode, map_comm]
  have h1 : ∀ z : A ⊗[R] A,
      TensorProduct.map (π : A →ₐc[R] B).toLinearMap LinearMap.id
          (TensorProduct.map (antipode R (A := A)) (antipode R (A := A)) z)
        = TensorProduct.map (antipode R (A := B)) (antipode R (A := A))
            (TensorProduct.map (π : A →ₐc[R] B).toLinearMap LinearMap.id z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.id_apply, toLinearMap_apply',
      map_antipode]
  rw [h1, map_toLinearMap_id_comul, coaction_eq_of_mem π ha]
  simp

noncomputable def rhoSub : A →ₗ[R] A ⊗[R] B :=
  (coaction π).toLinearMap - (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap

theorem rhoSub_apply (a : A) : rhoSub π a = coaction π a - a ⊗ₜ[R] 1 := rfl

theorem mem_hopfKer_iff_rhoSub (a : A) : a ∈ hopfKer π ↔ rhoSub π a = 0 := by
  rw [mem_hopfKer_iff, rhoSub_apply, sub_eq_zero]

theorem lTensor_coaction_comul {a : A} (ha : a ∈ hopfKer π) :
    (coaction π).toLinearMap.lTensor A (Coalgebra.comul (R := R) a)
      = (TensorProduct.assoc R A A B) (Coalgebra.comul (R := R) a ⊗ₜ[R] (1 : B)) := by
  set 𝓡 := ℛ R a
  let a₁ : (i : A × A) → Coalgebra.Repr R (𝓡.left i) (A × A) := fun i => ℛ R (𝓡.left i)
  let a₂ : (i : A × A) → Coalgebra.Repr R (𝓡.right i) (A × A) := fun i => ℛ R (𝓡.right i)
  have key := congr((TensorProduct.map LinearMap.id (π : A →ₐc[R] B).toLinearMap).lTensor A
    $(sum_tmul_tmul_eq 𝓡 a₁ a₂))
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply] at key

  have lhs : (coaction π).toLinearMap.lTensor A (Coalgebra.comul (R := R) a)
      = ∑ i ∈ 𝓡.index, ∑ k ∈ (a₂ i).index,
          𝓡.left i ⊗ₜ[R] ((a₂ i).left k ⊗ₜ[R] (π : A →ₐc[R] B).toLinearMap ((a₂ i).right k)) := by
    conv_lhs => rw [← 𝓡.eq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, coaction_repr π (a₂ i),
      TensorProduct.tmul_sum]
    rfl

  have rhs : ∑ i ∈ 𝓡.index, ∑ k ∈ (a₁ i).index,
        (a₁ i).left k ⊗ₜ[R] ((a₁ i).right k ⊗ₜ[R] (π : A →ₐc[R] B).toLinearMap (𝓡.right i))
      = (TensorProduct.assoc R A A B)
          ((Coalgebra.comul (R := R) (A := A)).rTensor B (coaction π a)) := by
    rw [coaction_repr π 𝓡, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.rTensor_tmul, ← (a₁ i).eq, TensorProduct.sum_tmul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.assoc_tmul]; rfl
  rw [lhs, ← key, rhs, coaction_eq_of_mem π ha, LinearMap.rTensor_tmul]

theorem lTensor_rhoSub_comul {a : A} (ha : a ∈ hopfKer π) :
    (rhoSub π).lTensor A (Coalgebra.comul (R := R) a) = 0 := by
  rw [rhoSub, LinearMap.lTensor_sub, LinearMap.sub_apply, lTensor_coaction_comul π ha, sub_eq_zero]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul x y => simp

theorem rTensor_coaction_comul [Coalgebra.IsCocomm R A] (a : A) :
    (coaction π).toLinearMap.rTensor A (Coalgebra.comul (R := R) a)
      = (TensorProduct.assoc R A B A).symm.toLinearMap
          ((TensorProduct.comm R A B).toLinearMap.lTensor A
            ((coaction π).toLinearMap.lTensor A (Coalgebra.comul (R := R) a))) := by
  set 𝓡 := ℛ R a
  let a₁ : (i : A × A) → Coalgebra.Repr R (𝓡.left i) (A × A) := fun i => ℛ R (𝓡.left i)
  let a₂ : (i : A × A) → Coalgebra.Repr R (𝓡.right i) (A × A) := fun i => ℛ R (𝓡.right i)
  let Ψ : A ⊗[R] (A ⊗[R] A) →ₗ[R] (A ⊗[R] B) ⊗[R] A :=
    (TensorProduct.assoc R A B A).symm.toLinearMap
      ∘ₗ (TensorProduct.map (π : A →ₐc[R] B).toLinearMap LinearMap.id).lTensor A
  have hΨ : ∀ x y z : A, Ψ (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = (x ⊗ₜ[R] π y) ⊗ₜ[R] z := by
    intro x y z
    simp only [Ψ, LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul, toLinearMap_apply']
  have key := congr(Ψ $(sum_tmul_tmul_eq 𝓡 a₁ a₂))
  simp only [map_sum, hΨ] at key
  have lhs : (coaction π).toLinearMap.rTensor A (Coalgebra.comul (R := R) a)
      = ∑ i ∈ 𝓡.index, ∑ k ∈ (a₁ i).index,
          ((a₁ i).left k ⊗ₜ[R] π ((a₁ i).right k)) ⊗ₜ[R] 𝓡.right i := by
    conv_lhs => rw [← 𝓡.eq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, coaction_repr π (a₁ i),
      TensorProduct.sum_tmul]
  have rhs : ∑ i ∈ 𝓡.index, ∑ k ∈ (a₂ i).index,
        (𝓡.left i ⊗ₜ[R] π ((a₂ i).left k)) ⊗ₜ[R] (a₂ i).right k
      = (TensorProduct.assoc R A B A).symm.toLinearMap
          ((TensorProduct.comm R A B).toLinearMap.lTensor A
            ((coaction π).toLinearMap.lTensor A (Coalgebra.comul (R := R) a))) := by
    conv_rhs => rw [← 𝓡.eq]
    simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_toLinearMap_id_comul' π (𝓡.right i), ← (a₂ i).eq]
    simp only [map_sum, TensorProduct.tmul_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      toLinearMap_apply']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul]
  rw [lhs, key, rhs]

theorem rTensor_rhoSub_comul [Coalgebra.IsCocomm R A] {a : A} (ha : a ∈ hopfKer π) :
    (rhoSub π).rTensor A (Coalgebra.comul (R := R) a) = 0 := by
  rw [rhoSub, LinearMap.rTensor_sub, LinearMap.sub_apply, rTensor_coaction_comul π a,
    lTensor_coaction_comul π ha, sub_eq_zero]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul x y => simp [LinearEquiv.coe_coe]

end Stability

section Structure

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)

noncomputable abbrev valL : ↥(hopfKer π) →ₗ[R] A := (hopfKer π).val.toLinearMap

@[simp] theorem valL_apply (s : ↥(hopfKer π)) : valL π s = (s : A) := rfl

theorem exact_valL_rhoSub : Function.Exact (valL π) (rhoSub π) := by
  intro a
  rw [← mem_hopfKer_iff_rhoSub]
  constructor
  · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨s, rfl⟩; exact s.2

noncomputable def ι₂A : ↥(hopfKer π) ⊗[R] ↥(hopfKer π) →ₐ[R] A ⊗[R] A :=
  Algebra.TensorProduct.map (hopfKer π).val (hopfKer π).val

noncomputable def ι₂ : ↥(hopfKer π) ⊗[R] ↥(hopfKer π) →ₗ[R] A ⊗[R] A := (ι₂A π).toLinearMap

theorem ι₂_eq_map : ι₂ π = TensorProduct.map (valL π) (valL π) :=
  TensorProduct.ext' fun _ _ => rfl

@[simp] theorem ι₂_tmul (s t : ↥(hopfKer π)) : ι₂ π (s ⊗ₜ[R] t) = (s : A) ⊗ₜ[R] (t : A) := rfl

theorem ι₂_mul (x y : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) : ι₂ π (x * y) = ι₂ π x * ι₂ π y :=
  map_mul (ι₂A π) x y

theorem ι₂_one : ι₂ π 1 = 1 := map_one (ι₂A π)

variable [Module.Flat R A] [Module.Flat R B] [Module.Flat R ↥(hopfKer π)]

theorem ι₂_injective : Function.Injective (ι₂ π) := by
  have h1 : Function.Injective ((valL π).lTensor ↥(hopfKer π)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h2 : Function.Injective ((valL π).rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [ι₂_eq_map, ← LinearMap.rTensor_comp_lTensor]
  exact h2.comp h1

noncomputable def ι₃ : ↥(hopfKer π) ⊗[R] (↥(hopfKer π) ⊗[R] ↥(hopfKer π)) →ₗ[R] A ⊗[R] (A ⊗[R] A) :=
  TensorProduct.map (valL π) (ι₂ π)

@[simp] theorem ι₃_tmul (s : ↥(hopfKer π)) (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    ι₃ π (s ⊗ₜ[R] z) = (s : A) ⊗ₜ[R] ι₂ π z := rfl

theorem ι₃_injective : Function.Injective (ι₃ π) := by
  have h1 : Function.Injective ((ι₂ π).lTensor ↥(hopfKer π)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (ι₂_injective π)
  have h2 : Function.Injective ((valL π).rTensor (A ⊗[R] A)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [ι₃, ← LinearMap.rTensor_comp_lTensor]
  exact h2.comp h1

variable [Coalgebra.IsCocomm R A]

theorem comul_coe_mem_range (s : ↥(hopfKer π)) :
    Coalgebra.comul (R := R) (s : A) ∈ LinearMap.range (ι₂ π) := by
  have ex1 : Function.Exact ((valL π).rTensor A) ((rhoSub π).rTensor A) :=
    Module.Flat.rTensor_exact A (exact_valL_rhoSub π)
  obtain ⟨w, hw⟩ := (ex1 _).mp (rTensor_rhoSub_comul π s.2)
  have hinj : Function.Injective ((valL π).rTensor (A ⊗[R] B)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hw2 : (rhoSub π).lTensor ↥(hopfKer π) w = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ←
      LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hw, lTensor_rhoSub_comul π s.2]
  have ex2 : Function.Exact ((valL π).lTensor ↥(hopfKer π)) ((rhoSub π).lTensor ↥(hopfKer π)) :=
    Module.Flat.lTensor_exact ↥(hopfKer π) (exact_valL_rhoSub π)
  obtain ⟨w2, hw2'⟩ := (ex2 _).mp hw2
  refine ⟨w2, ?_⟩
  rw [ι₂_eq_map, ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hw2', hw]

noncomputable def comulK : ↥(hopfKer π) →ₗ[R] ↥(hopfKer π) ⊗[R] ↥(hopfKer π) :=
  (LinearEquiv.ofInjective (ι₂ π) (ι₂_injective π)).symm.toLinearMap
    ∘ₗ ((Coalgebra.comul (R := R) (A := A)) ∘ₗ valL π).codRestrict (LinearMap.range (ι₂ π))
        (comul_coe_mem_range π)

@[simp] theorem ι₂_comulK (s : ↥(hopfKer π)) : ι₂ π (comulK π s) = Coalgebra.comul (R := R) (s : A)
  := by
  have h := LinearEquiv.ofInjective_symm_apply (f := ι₂ π) (h := ι₂_injective π)
    (((Coalgebra.comul (R := R) (A := A)) ∘ₗ valL π).codRestrict _ (comul_coe_mem_range π) s)
  exact h

noncomputable def counitK : ↥(hopfKer π) →ₗ[R] R := Coalgebra.counit ∘ₗ valL π

@[simp] theorem counitK_apply (s : ↥(hopfKer π)) : counitK π s = Coalgebra.counit (R := R) (s : A)
  := rfl

theorem rTensor_counitK (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    (valL π).lTensor R ((counitK π).rTensor ↥(hopfKer π) z)
      = (Coalgebra.counit (R := R) (A := A)).rTensor A (ι₂ π z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem lTensor_counitK (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    (valL π).rTensor R ((counitK π).lTensor ↥(hopfKer π) z)
      = (Coalgebra.counit (R := R) (A := A)).lTensor A (ι₂ π z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem ι₃_lTensor_comulK (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    ι₃ π ((comulK π).lTensor ↥(hopfKer π) z) = (Coalgebra.comul (R := R) (A := A)).lTensor A (ι₂ π
      z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem ι₃_assoc_rTensor_comulK (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    ι₃ π ((TensorProduct.assoc R _ _ _).toLinearMap ((comulK π).rTensor ↥(hopfKer π) z))
      = (TensorProduct.assoc R A A A).toLinearMap ((Coalgebra.comul (R := R) (A := A)).rTensor A
        (ι₂ π z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.rTensor_tmul, ι₂_tmul]
      rw [← ι₂_comulK π x]
      induction comulK π x using TensorProduct.inductionOn with
      | add c d hc hd => simp only [TensorProduct.add_tmul, map_add, hc, hd]
      | tmul c d => simp [LinearEquiv.coe_coe]

noncomputable instance instCoalgebra : Coalgebra R ↥(hopfKer π) where
  comul := comulK π
  counit := counitK π
  coassoc := by
    ext s
    apply ι₃_injective π
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      ι₃_assoc_rTensor_comulK, ι₃_lTensor_comulK, ι₂_comulK]
    exact LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := A)) (s : A)
  rTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL π).lTensor R) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul, valL_apply]
    rw [rTensor_counitK, ι₂_comulK, Coalgebra.rTensor_counit_comul]
  lTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL π).rTensor R) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul,
      valL_apply]
    rw [lTensor_counitK, ι₂_comulK, Coalgebra.lTensor_counit_comul]

theorem comul_def (s : ↥(hopfKer π)) : Coalgebra.comul (R := R) s = comulK π s := rfl

theorem counit_coe (s : ↥(hopfKer π)) : Coalgebra.counit (R := R) s = Coalgebra.counit (R := R) (s
  : A) := rfl

@[simp] theorem ι₂_comul (s : ↥(hopfKer π)) : ι₂ π (Coalgebra.comul (R := R) s) = Coalgebra.comul
  (R := R) (s : A) :=
  ι₂_comulK π s

theorem map_val_val_comul (s : ↥(hopfKer π)) :
    TensorProduct.map (valL π) (valL π) (Coalgebra.comul (R := R) s) = Coalgebra.comul (R := R) (s
      : A) := by
  rw [← ι₂_eq_map, ι₂_comul]

noncomputable instance instBialgebra : Bialgebra R ↥(hopfKer π) where
  counit_one := by rw [counit_coe]; simp
  mul_compr₂_counit := by
    ext a b
    exact (Bialgebra.counit_mul (R := R) (a : A) (b : A) : _)
  comul_one := by
    apply ι₂_injective π
    rw [ι₂_comul, ι₂_one]; simp
  mul_compr₂_comul := by
    ext a b
    apply ι₂_injective π
    change ι₂ π (Coalgebra.comul (R := R) (a * b)) = ι₂ π (Coalgebra.comul (R := R) a *
      Coalgebra.comul (R := R) b)
    rw [ι₂_mul, ι₂_comul, ι₂_comul, ι₂_comul, Subalgebra.coe_mul, Bialgebra.comul_mul]

noncomputable def antipodeK : ↥(hopfKer π) →ₗ[R] ↥(hopfKer π) where
  toFun s := ⟨antipode R (s : A), antipode_mem π s.2⟩
  map_add' s t := by ext; simp
  map_smul' r s := by ext; simp

@[simp] theorem coe_antipodeK (s : ↥(hopfKer π)) : ((antipodeK π s : ↥(hopfKer π)) : A) = antipode
  R (s : A) := rfl

theorem val_mul'_rTensor_antipodeK (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    ((LinearMap.mul' R ↥(hopfKer π) ((antipodeK π).rTensor _ z) : ↥(hopfKer π)) : A)
      = LinearMap.mul' R A ((antipode R (A := A)).rTensor A (ι₂ π z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y => simp

theorem val_mul'_lTensor_antipodeK (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    ((LinearMap.mul' R ↥(hopfKer π) ((antipodeK π).lTensor _ z) : ↥(hopfKer π)) : A)
      = LinearMap.mul' R A ((antipode R (A := A)).lTensor A (ι₂ π z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y => simp

noncomputable instance instHopfAlgebra : HopfAlgebra R ↥(hopfKer π) where
  antipode := antipodeK π
  mul_antipode_rTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [val_mul'_rTensor_antipodeK, ι₂_comul, mul_antipode_rTensor_comul_apply, counit_coe]
  mul_antipode_lTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [val_mul'_lTensor_antipodeK, ι₂_comul, mul_antipode_lTensor_comul_apply, counit_coe]

@[simp] theorem coe_antipode (s : ↥(hopfKer π)) : ((antipode R s : ↥(hopfKer π)) : A) = antipode R
  (s : A) := rfl

theorem ι₂_comm (z : ↥(hopfKer π) ⊗[R] ↥(hopfKer π)) :
    ι₂ π (TensorProduct.comm R _ _ z) = TensorProduct.comm R A A (ι₂ π z) := by
  rw [ι₂_eq_map, map_comm]

instance instIsCocomm : Coalgebra.IsCocomm R ↥(hopfKer π) where
  comm_comp_comul := by
    ext s
    apply ι₂_injective π
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ι₂_comm, ι₂_comul, Coalgebra.comm_comul]

noncomputable def hopfKerVal : ↥(hopfKer π) →ₐc[R] A :=
  { (hopfKer π).val with
    map_smul' := fun r x => by simp
    counit_comp := rfl
    map_comp_comul := by
      ext s
      change TensorProduct.map (valL π) (valL π) (Coalgebra.comul (R := R) s) = Coalgebra.comul (R
        := R) (s : A)
      exact map_val_val_comul π s }

@[simp] theorem hopfKerVal_apply (s : ↥(hopfKer π)) : hopfKerVal π s = (s : A) := rfl

theorem hopfKerVal_injective : Function.Injective (hopfKerVal π) := Subtype.val_injective

end Structure

end HopfKerHopf

section HopfIdealQuotientMaps

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

/-- The factor map between quotients by Hopf ideals, as a bialgebra hom. -/
def quotientFactorBialgHom {I J : Ideal H} [I.IsHopfIdeal R] [J.IsHopfIdeal R]
    (hIJ : I ≤ J) : H ⧸ I →ₐc[R] H ⧸ J :=
  BialgHom.ofAlgHom (Ideal.Quotient.factorₐ R hIJ)
    (by
      ext y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp)
    (by
      ext y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hz : ∀ z : H ⊗[R] H,
          (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hIJ)
            (Ideal.Quotient.factorₐ R hIJ))
            (TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
              (Ideal.Quotient.mkₐ R I).toLinearMap z) =
            TensorProduct.map (Ideal.Quotient.mkₐ R J).toLinearMap
              (Ideal.Quotient.mkₐ R J).toLinearMap z := by
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul a b => simp
        | add z w hz hw => simp only [map_add, hz, hw]
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.Quotient.comul_mk]
      rw [hz]
      rfl)

@[simp] theorem quotientFactorBialgHom_apply_mk {I J : Ideal H} [I.IsHopfIdeal R]
    [J.IsHopfIdeal R] (hIJ : I ≤ J) (x : H) :
    quotientFactorBialgHom (R := R) hIJ (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J x := rfl

theorem quotientFactorBialgHom_surjective {I J : Ideal H} [I.IsHopfIdeal R]
    [J.IsHopfIdeal R] (hIJ : I ≤ J) :
    Function.Surjective (quotientFactorBialgHom (R := R) hIJ) :=
  Ideal.Quotient.factor_surjective hIJ

theorem quotientFactorBialgHom_comp {I J : Ideal H} [I.IsHopfIdeal R] [J.IsHopfIdeal R]
    (hIJ : I ≤ J) :
    (quotientFactorBialgHom (R := R) hIJ).comp (Bialgebra.Quotient.mkBialgHom (R := R) I) =
      Bialgebra.Quotient.mkBialgHom (R := R) J := by
  ext x; rfl

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Algebra maps out of a quotient by a Hopf ideal, as maps vanishing on the ideal. -/
def quotientPointsEquiv (I : Ideal H) [I.IsHopfIdeal R] :
    (H ⧸ I →ₐ[R] A) ≃ {f : H →ₐ[R] A // ∀ x ∈ I, f x = 0} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ R I), fun x hx => by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun f := Ideal.Quotient.liftₐ I f.1 f.2
  left_inv g := Ideal.Quotient.algHom_ext R (Ideal.Quotient.liftₐ_comp I _ _)
  right_inv f := Subtype.ext (Ideal.Quotient.liftₐ_comp I f.1 f.2)

end HopfIdealQuotientMaps

end HopfAlgebra
