/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Composition

/-!
# Balanced induction and commutative scalar extension

Let `k : Type u` and `R : Type v` be commutative rings and `φ : k →+* R`. On modules with
carrier universe `max u v w`, balanced induction along `φ` is naturally isomorphic to tensor
scalar extension `M ↦ R ⊗_{k,φ} M`. The comparison is the isomorphism between the two left
adjoints of restriction of scalars.

It sends the balanced class `tensor φ M r m` to `r ⊗ₜ[k,φ] m`; its inverse sends the pure
tensor to that balanced class. In particular, the unit class at `r=1` is preserved.
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

universe u v w

namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [CommRing k] [CommRing R] (φ : k →+* R)

/-- Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, and `w` a
carrier-universe parameter. There is a natural isomorphism `ModuleCat.induceScalars.{u,v,w} φ
≅ ModuleCat.extendScalars.{u,v,max u v w} φ`, on modules of universe `max u v w`. It is
induced by the two induction/extension adjunctions with the same restriction-of-scalars
functor. -/
noncomputable def commutativeIso :
    ModuleCat.induceScalars.{u, v, w} φ ≅
      ModuleCat.extendScalars.{u, v, max u v w} φ :=
  Adjunction.leftAdjointUniq
    (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ)
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v} φ)

/-- Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, `M : ModuleCat.{max u v
w} k`, and `m∈M`. The component of `commutativeIso φ` sends `tensor φ M 1 m` to `(1 : R)
⊗ₜ[k,φ] m`, where the `k`-action on `R` is through `φ`. -/
theorem commutativeIso_hom_unit (M : ModuleCat.{max u v w} k) (m : M) :
    (commutativeIso.{u, v, w} φ).hom.app M (tensor φ M 1 m) = (1 : R) ⊗ₜ[k,φ] m := by
  let N : ModuleCat.{max u v w} R := (ModuleCat.extendScalars.{u, v, max u v w} φ).obj M
  let G := ModuleCat.restrictScalars.{max u v w} φ
  let μ : (ModuleCat.induceScalars.{u, v, w} φ).obj M ⟶ N :=
    (commutativeIso.{u, v, w} φ).hom.app M
  have he : (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).homEquiv M N μ =
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v} φ).unit.app M :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ)
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v} φ) M
  have hm := congrArg (fun q : M ⟶ G.obj N => (show N from q m)) he
  have hl : (show N from
      (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).homEquiv M N μ m) =
      μ (tensor φ M 1 m) := nativeHomEquiv_apply φ M N μ m
  have hr : (show N from
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v} φ).unit.app M m) =
      (1 : R) ⊗ₜ[k,φ] m :=
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{max u v w, u, v} φ M m
  exact hl.symm.trans (hm.trans hr)

/-- Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, `M : ModuleCat.{max u v
w} k`, `r∈R`, and `m∈M`. Then `(commutativeIso φ).hom.app M (tensor φ M r m) = r ⊗ₜ[k,φ] m`.
Thus the comparison preserves both entries of each balanced pure tensor. -/
theorem commutativeIso_hom_tensor (M : ModuleCat.{max u v w} k) (r : R) (m : M) :
    (commutativeIso.{u, v, w} φ).hom.app M (tensor φ M r m) = r ⊗ₜ[k,φ] m := by
  let N : ModuleCat.{max u v w} R := (ModuleCat.extendScalars.{u, v, max u v w} φ).obj M
  let μ : (ModuleCat.induceScalars.{u, v, w} φ).obj M ⟶ N :=
    (commutativeIso.{u, v, w} φ).hom.app M
  have hi : tensor φ M r m = r • tensor φ M 1 m := by
    simpa only [mul_one] using (smul_tensor φ M r 1 m).symm
  have hu : μ (tensor φ M 1 m) = (show N from (1 : R) ⊗ₜ[k,φ] m) :=
    commutativeIso_hom_unit φ M m
  have h₁ : μ (tensor φ M r m) = r • μ (tensor φ M 1 m) :=
    (congrArg μ hi).trans (μ.hom.map_smul r (tensor φ M 1 m))
  have h₂ : r • μ (tensor φ M 1 m) = r • (show N from (1 : R) ⊗ₜ[k,φ] m) :=
    congrArg (fun x : N => r • x) hu
  have h₃ : r • (show N from (1 : R) ⊗ₜ[k,φ] m) = (show N from r ⊗ₜ[k,φ] m) := by
    change (r * 1) ⊗ₜ[k,φ] m = r ⊗ₜ[k,φ] m
    rw [mul_one]
  exact h₁.trans (h₂.trans h₃)

/-- Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, `M : ModuleCat.{max u v
w} k`, `r∈R`, and `m∈M`. Then `(commutativeIso φ).inv.app M (r ⊗ₜ[k,φ] m) = tensor φ M r m`,
the corresponding class in balanced induction. -/
theorem commutativeIso_inv_tensor (M : ModuleCat.{max u v w} k) (r : R) (m : M) :
    (commutativeIso.{u, v, w} φ).inv.app M (r ⊗ₜ[k,φ] m) = tensor φ M r m := by
  let e := ((commutativeIso.{u, v, w} φ).app M).toLinearEquiv
  change e.symm (r ⊗ₜ[k,φ] m) = tensor φ M r m
  have h : e (tensor φ M r m) = r ⊗ₜ[k,φ] m := commutativeIso_hom_tensor φ M r m
  exact (congrArg e.symm h).symm.trans (e.symm_apply_apply _)

end ModuleCat.RingHomInduction
