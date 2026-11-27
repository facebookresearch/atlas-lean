/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Algebra_PointDerivations.lean`,
`Theorems/Thm_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType.lean`
and
`P2M/Sol/S_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType

public import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic

open scoped TensorProduct

/-!
# Point derivations

A point derivation at a `k`-point `ev : A →ₐ[k] k` of a `k`-algebra `A` is
a `k`-linear map `D : A →ₗ[k] M` satisfying the Leibniz rule
`D (a * b) = ev a • D b + ev b • D a`. They form a submodule of
`A →ₗ[k] M`, functorial in `M`, and vanish on constants and on the image
of `algebraMap k A`.
-/

@[expose] public section

universe u v w w' w''

namespace Algebra

/-- Point derivations at a `k`-point `ev` of a `k`-algebra `A` with values
in a `k`-module `M`. -/
def PointDerivations (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (ev : A →ₐ[k] k) (M : Type w) [AddCommGroup M] [Module k M] : Submodule k (A →ₗ[k] M) where
  carrier := {D | ∀ a b : A, D (a * b) = ev a • D b + ev b • D a}
  add_mem' := by
    intro D D' hD hD' a b
    simp only [LinearMap.add_apply, hD a b, hD' a b, smul_add]
    ac_rfl
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, hD a b, smul_add, smul_comm c]

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →ₐ[k] k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

theorem mem_iff (D : A →ₗ[k] M) :
    D ∈ PointDerivations k A ev M ↔ ∀ a b : A, D (a * b) = ev a • D b + ev b • D a :=
  Iff.rfl

theorem apply_mul {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (a b : A) :
    D (a * b) = ev a • D b + ev b • D a := hD a b

theorem apply_one {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, show ev 1 = 1 from map_one ev, one_smul] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem apply_algebraMap {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (c : k) :
    D (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, apply_one hD, smul_zero]

/-- Functoriality of point derivations in the coefficient module. -/
def map (ev : A →ₐ[k] k) (φ : M →ₗ[k] M') :
    ↥(PointDerivations k A ev M) →ₗ[k] ↥(PointDerivations k A ev M') where
  toFun D := ⟨φ.comp D.1, fun a b => by
    simp only [LinearMap.comp_apply, D.2 a b, map_add, map_smul]⟩
  map_add' D D' := by ext a; simp
  map_smul' c D := by ext a; simp

@[simp] theorem map_apply_coe (ev : A →ₐ[k] k) (φ : M →ₗ[k] M')
    (D : ↥(PointDerivations k A ev M)) (a : A) :
    (map ev φ D : A →ₗ[k] M') a = φ (D.1 a) := rfl

theorem map_id (ev : A →ₐ[k] k) (D : ↥(PointDerivations k A ev M)) :
    map ev (LinearMap.id : M →ₗ[k] M) D = D := by
  ext a; rfl

theorem map_comp {M'' : Type w''} [AddCommGroup M''] [Module k M''] (ev : A →ₐ[k] k)
    (φ : M →ₗ[k] M') (ψ : M' →ₗ[k] M'') (D : ↥(PointDerivations k A ev M)) :
    map ev (ψ.comp φ) D = map ev ψ (map ev φ D) := by
  ext a; rfl

def quotientSubmodule (ev : A →ₐ[k] k) : Submodule k A :=
  Submodule.span k {(1 : A)} ⊔
    ((RingHom.ker ev.toRingHom ^ 2 : Ideal A).restrictScalars k)

theorem ev_apply_algebraMap (ev : A →ₐ[k] k) (c : k) :
    ev (algebraMap k A c) = c := by
  simpa using AlgHom.commutes ev c

theorem sub_algebraMap_mem_ker (ev : A →ₐ[k] k) (a : A) :
    a - algebraMap k A (ev a) ∈ RingHom.ker ev.toRingHom := by
  rw [RingHom.mem_ker, map_sub]
  change ev a - ev (algebraMap k A (ev a)) = 0
  rw [ev_apply_algebraMap ev, sub_self]

theorem quotientSubmodule_le_ker (ev : A →ₐ[k] k)
    (D : ↥(PointDerivations k A ev M)) :
    quotientSubmodule ev ≤ LinearMap.ker (D : A →ₗ[k] M) := by
  apply sup_le
  · rw [Submodule.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact apply_one D.2
  · intro x hx
    rw [Submodule.restrictScalars_mem, pow_two] at hx
    rw [LinearMap.mem_ker]
    refine Submodule.smul_induction_on
      (p := fun y => (D : A →ₗ[k] M) y = 0) hx ?_ ?_
    · intro a ha b hb
      show (D : A →ₗ[k] M) (a * b) = 0
      have ha0 : ev a = 0 := (RingHom.mem_ker).mp ha
      have hb0 : ev b = 0 := (RingHom.mem_ker).mp hb
      rw [apply_mul D.2, ha0, hb0, zero_smul, zero_smul, add_zero]
    · intro x y hx hy
      show (D : A →ₗ[k] M) (x + y) = 0
      rw [map_add, hx, hy, add_zero]

def resMap (ev : A →ₐ[k] k) (M : Type w) [AddCommGroup M] [Module k M] :
    ↥(PointDerivations k A ev M) →ₗ[k] ((A ⧸ quotientSubmodule ev) →ₗ[k] M) where
  toFun D := (quotientSubmodule ev).liftQ (D : A →ₗ[k] M)
    (quotientSubmodule_le_ker ev D)
  map_add' D D' := by ext a; rfl
  map_smul' c D := by ext a; rfl

theorem quotient_mk_mul (ev : A →ₐ[k] k) (a b : A) :
    (Submodule.Quotient.mk (a * b) : A ⧸ quotientSubmodule ev) =
      ev a • Submodule.Quotient.mk b + ev b • Submodule.Quotient.mk a := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have h : a * b - (ev a • b + ev b • a) =
      (a - algebraMap k A (ev a)) * (b - algebraMap k A (ev b)) -
        algebraMap k A (ev a * ev b) := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [h]
  refine Submodule.sub_mem _ ?_ ?_
  · apply Submodule.mem_sup_right
    rw [Submodule.restrictScalars_mem, pow_two]
    exact Ideal.mul_mem_mul (sub_algebraMap_mem_ker ev a)
      (sub_algebraMap_mem_ker ev b)
  · apply Submodule.mem_sup_left
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

def extMap (ev : A →ₐ[k] k) (M : Type w) [AddCommGroup M] [Module k M] :
    ((A ⧸ quotientSubmodule ev) →ₗ[k] M) →ₗ[k] ↥(PointDerivations k A ev M) where
  toFun f := ⟨f ∘ₗ (quotientSubmodule ev).mkQ, fun a b => by
    show f (Submodule.Quotient.mk (a * b)) =
      ev a • f (Submodule.Quotient.mk b) + ev b • f (Submodule.Quotient.mk a)
    rw [quotient_mk_mul ev, map_add, map_smul, map_smul]⟩
  map_add' f g := by ext a; rfl
  map_smul' c f := by ext a; rfl

noncomputable def resEquiv (ev : A →ₐ[k] k) (M : Type w)
    [AddCommGroup M] [Module k M] :
    ↥(PointDerivations k A ev M) ≃ₗ[k] ((A ⧸ quotientSubmodule ev) →ₗ[k] M) :=
  LinearEquiv.ofLinearMap (resMap ev M) (extMap ev M)
    (by
      apply LinearMap.ext; intro f; apply LinearMap.ext; intro x
      induction x using Submodule.Quotient.induction_on with
      | H a => rfl)
    (by
      apply LinearMap.ext; intro D; apply Subtype.ext; apply LinearMap.ext
      intro a; rfl)

theorem res_map (ev : A →ₐ[k] k) {M : Type w} {M' : Type w'}
    [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
    (g : M →ₗ[k] M') (D : ↥(PointDerivations k A ev M)) :
    resMap ev M' (map ev g D) = g ∘ₗ resMap ev M D := by
  apply LinearMap.ext; intro x
  induction x using Submodule.Quotient.induction_on with
  | H a => rfl

theorem finite_quotient (ev : A →ₐ[k] k) [Algebra.FiniteType k A] :
    Module.Finite k (A ⧸ quotientSubmodule ev) := by
  classical
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker ev.toRingHom) :
    (RingHom.ker ev.toRingHom).FG)
  refine Module.Finite.of_surjective
    (Fintype.linearCombination k
      (fun i : ↥s => (Submodule.Quotient.mk (i : A) :
        A ⧸ quotientSubmodule ev))) ?_
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    have hm : a - algebraMap k A (ev a) ∈ Submodule.span A (s : Set A) := by
      rw [hs]; exact sub_algebraMap_mem_ker ev a
    rw [Submodule.mem_span_finset] at hm
    obtain ⟨c, -, hc⟩ := hm
    refine ⟨fun i => ev (c i), ?_⟩
    rw [Fintype.linearCombination_apply]
    have hsum : (∑ i : ↥s, ev (c ↑i) •
        (Submodule.Quotient.mk (↑i : A) : A ⧸ quotientSubmodule ev)) =
        Submodule.Quotient.mk (∑ i ∈ s, algebraMap k A (ev (c i)) * i) := by
      rw [← Finset.sum_coe_sort s (fun i => algebraMap k A (ev (c i)) * i)]
      simp only [← Algebra.smul_def, ← Submodule.Quotient.mk_smul]
      exact (map_sum ((quotientSubmodule ev).mkQ) _ _).symm
    rw [hsum, Submodule.Quotient.eq]
    simp only [smul_eq_mul] at hc
    have hrw : (∑ i ∈ s, algebraMap k A (ev (c i)) * i) - a =
        (∑ i ∈ s, (algebraMap k A (ev (c i)) - c i) * i) -
          algebraMap k A (ev a) := by
      rw [Finset.sum_congr rfl
        (fun i _ => sub_mul (algebraMap k A (ev (c i))) (c i) i),
        Finset.sum_sub_distrib, hc]
      ring
    rw [hrw]
    refine Submodule.sub_mem _ ?_ ?_
    · apply Submodule.mem_sup_right
      rw [Submodule.restrictScalars_mem, pow_two]
      refine Submodule.sum_mem _ (fun i hi => Ideal.mul_mem_mul ?_ ?_)
      · have hneg := (RingHom.ker ev.toRingHom).neg_mem
          (sub_algebraMap_mem_ker ev (c i))
        rwa [neg_sub] at hneg
      · rw [← hs]; exact Submodule.subset_span hi
    · apply Submodule.mem_sup_left
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The canonical identification of point derivations with values in `M`
with point derivations with values in `k`, tensored with `M`. -/
noncomputable def tensorEquiv (ev : A →ₐ[k] k) [Algebra.FiniteType k A]
    (M : Type w) [AddCommGroup M] [Module k M] :
    ↥(PointDerivations k A ev M) ≃ₗ[k]
      (↥(PointDerivations k A ev k) ⊗[k] M) :=
  haveI := finite_quotient ev
  (resEquiv ev M).trans
    ((dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) M).symm.trans
      (_root_.TensorProduct.congr (resEquiv ev k).symm (LinearEquiv.refl k M)))

theorem dualTensorHom_lTensor (ev : A →ₐ[k] k)
    {M : Type w} {M' : Type w'} [AddCommGroup M] [Module k M]
    [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
    (x : Module.Dual k (A ⧸ quotientSubmodule ev) ⊗[k] M) :
    dualTensorHom k (A ⧸ quotientSubmodule ev) M'
        (LinearMap.lTensor (Module.Dual k (A ⧸ quotientSubmodule ev)) g x) =
      g ∘ₗ dualTensorHom k (A ⧸ quotientSubmodule ev) M x := by
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul f m =>
    apply LinearMap.ext; intro t
    simp [LinearMap.lTensor_tmul, dualTensorHom_apply, map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, LinearMap.comp_add]

/-- The tensor identification is natural in the coefficient module. -/
theorem tensorEquiv_natural (ev : A →ₐ[k] k)
    [Algebra.FiniteType k A] {M : Type w} {M' : Type w'}
    [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
    (g : M →ₗ[k] M') (δ : ↥(PointDerivations k A ev M)) :
    tensorEquiv ev M' (map ev g δ) =
      LinearMap.lTensor (↥(PointDerivations k A ev k)) g
        (tensorEquiv ev M δ) := by
  haveI := finite_quotient ev
  have h1 : resEquiv ev M' (map ev g δ) = g ∘ₗ resEquiv ev M δ :=
    res_map ev g δ
  have h2 : (dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) M').symm
        (g ∘ₗ resEquiv ev M δ) =
      LinearMap.lTensor (Module.Dual k (A ⧸ quotientSubmodule ev)) g
        ((dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) M).symm
          (resEquiv ev M δ)) := by
    apply (dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) M').injective
    rw [LinearEquiv.apply_symm_apply]
    show g ∘ₗ resEquiv ev M δ =
      dualTensorHom k (A ⧸ quotientSubmodule ev) M'
        (LinearMap.lTensor (Module.Dual k (A ⧸ quotientSubmodule ev)) g
          ((dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) M).symm
            (resEquiv ev M δ)))
    rw [dualTensorHom_lTensor ev]
    congr 1
    exact ((dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) M).apply_symm_apply
      _).symm
  have h3 : ∀ y : Module.Dual k (A ⧸ quotientSubmodule ev) ⊗[k] M,
      _root_.TensorProduct.congr (resEquiv ev k).symm (LinearEquiv.refl k M')
          (LinearMap.lTensor (Module.Dual k (A ⧸ quotientSubmodule ev)) g y) =
        LinearMap.lTensor (↥(PointDerivations k A ev k)) g
          (_root_.TensorProduct.congr (resEquiv ev k).symm (LinearEquiv.refl k M) y) := by
    intro y
    induction y using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul f m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [tensorEquiv, LinearEquiv.trans_apply]
  rw [h1, h2, h3]

/-- The tensor identification sends a derivation over `k` to itself
tensored with `1`. -/
theorem tensorEquiv_self (ev : A →ₐ[k] k) [Algebra.FiniteType k A]
    (δ : ↥(PointDerivations k A ev k)) :
    tensorEquiv ev k δ = δ ⊗ₜ[k] (1 : k) := by
  haveI := finite_quotient ev
  have h : (dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) k).symm
        (resEquiv ev k δ) =
      (resEquiv ev k δ) ⊗ₜ[k] (1 : k) := by
    apply (dualTensorHomEquiv k (A ⧸ quotientSubmodule ev) k).injective
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext; intro t
    show resEquiv ev k δ t =
      dualTensorHom k (A ⧸ quotientSubmodule ev) k
        (resEquiv ev k δ ⊗ₜ[k] (1 : k)) t
    rw [dualTensorHom_apply, smul_eq_mul, mul_one]
  simp only [tensorEquiv, LinearEquiv.trans_apply, h,
    _root_.TensorProduct.congr_tmul, LinearEquiv.symm_apply_apply,
    LinearEquiv.refl_apply]

/-- For a finite-type algebra over a field, point derivations with values in
any coefficient module are obtained from point derivations with values in the
field by tensoring, naturally in the coefficient module. -/
theorem exists_linearEquiv_tensor_forall_map_eq_of_finiteType
    (ev : A →ₐ[k] k) [Algebra.FiniteType k A] :
    ∃ Ψ : ∀ (M : Type u) [AddCommGroup M] [Module k M],
        ↥(PointDerivations k A ev M) ≃ₗ[k]
          (↥(PointDerivations k A ev k) ⊗[k] M),
      (∀ (M : Type u) (M' : Type u) [AddCommGroup M] [Module k M]
          [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
          (δ : ↥(PointDerivations k A ev M)),
        Ψ M' (map ev g δ) =
          LinearMap.lTensor (↥(PointDerivations k A ev k)) g (Ψ M δ)) ∧
      (∀ δ : ↥(PointDerivations k A ev k), Ψ k δ = δ ⊗ₜ[k] (1 : k)) :=
  ⟨fun M _ _ => tensorEquiv ev M,
    fun M M' _ _ _ _ g δ => tensorEquiv_natural ev g δ,
    fun δ => tensorEquiv_self ev δ⟩

end PointDerivations

end Algebra
