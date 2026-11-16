/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/TensorProduct.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.CochainBraiding
public import MathlibExt.CategoryTheory.DGSource.DGCategory
public import MathlibExt.CategoryTheory.DGSource.EnrichedTensorProduct

import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Tensor products of differential graded categories

The tensor product of two differential graded categories `C` and `D` over `R` has the pairs
`(X, Y)` as objects, and its Hom complex from `(X, Y)` to `(X', Y')` is the tensor product
`Hom(X, X') ⊗ Hom(Y, Y')` of cochain complexes. It is the tensor product
`MathlibExt.DGSource.tensorEnrichedCategory` of categories enriched in cochain complexes of `R`-modules,
whose braiding is the Koszul braiding `MathlibExt.DGSource.koszulBraidedCategory`.

This file makes the structure explicit on homogeneous morphisms. For `f : X ⟶ X'` of degree `p`
and `g : Y ⟶ Y'` of degree `q`, the morphism `f ⊗ g : (X, Y) ⟶ (X', Y')` of degree `p + q` is
`MathlibExt.DGSource.dgTensorHom f g`. Every morphism of the tensor product is a sum of these, and

* `d (f ⊗ g) = d f ⊗ g + (-1) ^ p • f ⊗ d g`;
* `dgComp (f ⊗ g) (f' ⊗ g') = (-1) ^ (q * p') • dgComp f f' ⊗ dgComp g g'`, where `p'` is the
  degree of `f'`: composition moves `g` past `f'`, with the Koszul sign;
* the identity of `(X, Y)` is `1_X ⊗ 1_Y`.

Tensor products are how DG bimodules are compared with modules: a DG bimodule with a left action
of `A` and a right action of `B` is a right DG module over the tensor product of the opposite of
`A` with `B`.

## Main definitions

* `MathlibExt.DGSource.dgTensorHom`: the tensor product of two homogeneous morphisms.

## Main results

* `MathlibExt.DGSource.dgTensorHom_induction`: the tensor products of homogeneous morphisms span every
  `R`-module of morphisms of a fixed degree.
* `MathlibExt.DGSource.dgDifferential_dgTensorHom`: the differential of a tensor product of morphisms.
* `MathlibExt.DGSource.dgCompMap_tensor`: composition on a homogeneous summand of the tensor product.
* `MathlibExt.DGSource.dgComp_dgTensorHom`: composition of tensor products of morphisms, with its Koszul
  sign.
* `MathlibExt.DGSource.dgId_tensor`: identities are tensor products of identities.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
* G. M. Kelly, *Basic concepts of enriched category theory*, Section 1.4.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex

namespace MathlibExt.DGSource

universe v u₁ u₂

variable (R : Type v) [CommRing R] {C : Type u₁} {D : Type u₂} [DGCategory R C] [DGCategory R D]

/-- The tensor product `f ⊗ g : X ⟶ Y` in the tensor product of two differential graded
categories, of degree `n = p + q`, of a morphism `f : X.1 ⟶ Y.1` of degree `p` and a morphism
`g : X.2 ⟶ Y.2` of degree `q`. -/
noncomputable def dgTensorHom {X Y : C × D} {p q n : ℤ} (f : DGHom R p X.1 Y.1)
    (g : DGHom R q X.2 Y.2) (h : p + q = n) : DGHom R n X Y :=
  (ιTensorObj (dgHomComplex R X.1 Y.1) (dgHomComplex R X.2 Y.2) p q n h).hom (f ⊗ₜ g)

/-- The tensor product of two homogeneous morphisms is the image of `f ⊗ₜ g` under the inclusion
of the bidegree-`(p, q)` summand of the tensor product of the two Hom complexes. -/
theorem dgTensorHom_def {X Y : C × D} {p q n : ℤ} (f : DGHom R p X.1 Y.1)
    (g : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgTensorHom R f g h =
      (ιTensorObj (dgHomComplex R X.1 Y.1) (dgHomComplex R X.2 Y.2) p q n h).hom (f ⊗ₜ g) :=
  (rfl)

section Bilinear

variable {R} {X Y : C × D} {p q n : ℤ}

@[simp]
theorem zero_dgTensorHom (g : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgTensorHom R (0 : DGHom R p X.1 Y.1) g h = 0 := by
  rw [dgTensorHom, TensorProduct.zero_tmul, map_zero]

@[simp]
theorem dgTensorHom_zero (f : DGHom R p X.1 Y.1) (h : p + q = n) :
    dgTensorHom R f (0 : DGHom R q X.2 Y.2) h = 0 := by
  rw [dgTensorHom, TensorProduct.tmul_zero, map_zero]

@[simp]
theorem add_dgTensorHom (f f' : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgTensorHom R (f + f') g h = dgTensorHom R f g h + dgTensorHom R f' g h := by
  rw [dgTensorHom, dgTensorHom, dgTensorHom, TensorProduct.add_tmul, map_add]

@[simp]
theorem dgTensorHom_add (f : DGHom R p X.1 Y.1) (g g' : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgTensorHom R f (g + g') h = dgTensorHom R f g h + dgTensorHom R f g' h := by
  rw [dgTensorHom, dgTensorHom, dgTensorHom, TensorProduct.tmul_add, map_add]

@[simp]
theorem neg_dgTensorHom (f : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgTensorHom R (-f) g h = -dgTensorHom R f g h := by
  rw [dgTensorHom, dgTensorHom, TensorProduct.neg_tmul, map_neg]

@[simp]
theorem dgTensorHom_neg (f : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgTensorHom R f (-g) h = -dgTensorHom R f g h := by
  rw [dgTensorHom, dgTensorHom, TensorProduct.tmul_neg, map_neg]

@[simp]
theorem smul_dgTensorHom (r : R) (f : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2)
    (h : p + q = n) : dgTensorHom R (r • f) g h = r • dgTensorHom R f g h := by
  rw [dgTensorHom, dgTensorHom, ← TensorProduct.smul_tmul', map_smul]

@[simp]
theorem dgTensorHom_smul (r : R) (f : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2)
    (h : p + q = n) : dgTensorHom R f (r • g) h = r • dgTensorHom R f g h := by
  rw [dgTensorHom, dgTensorHom, TensorProduct.tmul_smul, map_smul]

end Bilinear

/-- **Induction on morphisms of a tensor product of differential graded categories**: a property
of the morphisms of degree `n` which holds for every tensor product of homogeneous morphisms and
is closed under addition holds for every morphism of degree `n`. -/
@[elab_as_elim]
theorem dgTensorHom_induction {X Y : C × D} {n : ℤ} {motive : DGHom R n X Y → Prop}
    (tmul : ∀ (p q : ℤ) (h : p + q = n) (f : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2),
      motive (dgTensorHom R f g h))
    (add : ∀ x y, motive x → motive y → motive (x + y)) (x : DGHom R n X Y) : motive x := by
  let S : Submodule R (DGHom R n X Y) := Submodule.span R
    {y | ∃ (p q : ℤ) (h : p + q = n) (f : DGHom R p X.1 Y.1) (g : DGHom R q X.2 Y.2),
      dgTensorHom R f g h = y}
  -- The quotient by the span of the tensor products vanishes on every summand of the
  -- tensor product of Hom complexes, hence everywhere.
  have hmk : ModuleCat.ofHom S.mkQ = 0 := by
    refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦
      ModuleCat.MonoidalCategory.tensor_ext fun f g ↦ ?_
    have hmem : dgTensorHom R f g h ∈ S := Submodule.subset_span ⟨p, q, h, f, g, rfl⟩
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Limits.comp_zero, ModuleCat.hom_zero, LinearMap.zero_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hmem
  have hx : x ∈ S := (Submodule.Quotient.mk_eq_zero S).mp
    (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmk) x)
  -- `motive` need not be closed under scalars, so induct on the property `∀ r, motive (r • y)`.
  suffices ∀ r : R, motive (r • x) by simpa using this 1
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, h, f, g, rfl⟩ := hy
    intro r
    rw [← smul_dgTensorHom]
    exact tmul p q h (r • f) g
  | zero => exact fun _ ↦ by simpa using tmul n 0 (add_zero n) 0 0
  | add y z _ _ hy hz => exact fun r ↦ by simpa [smul_add] using add _ _ (hy r) (hz r)
  | smul s y _ hy => exact fun r ↦ by simpa [smul_smul] using hy (r * s)

/-- The differential of a tensor product of homogeneous morphisms differentiates each factor, with
the Koszul sign `(-1) ^ p` of the degree `p` of the first factor on the second term. -/
theorem dgDifferential_dgTensorHom {X Y : C × D} {p q n : ℤ} (f : DGHom R p X.1 Y.1)
    (g : DGHom R q X.2 Y.2) (h : p + q = n) :
    dgDifferential R n (dgTensorHom R f g h) =
      dgTensorHom R (dgDifferential R p f) g (by omega) +
        p.negOnePow • dgTensorHom R f (dgDifferential R q g) (by omega) := by
  have key := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (ι_tensorObj_d (dgHomComplex R X.1 Y.1) (dgHomComplex R X.2 Y.2) p q n h)) (f ⊗ₜ g)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_add, ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply,
    curriedTensor_map_app, curriedTensor_obj_map] at key
  rw [ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at key
  exact key

/-- Composition in the tensor product on the summand of bidegrees `((p, q), (p', q'))`: interchange
the two middle factors, with the Koszul sign `(-1) ^ (q * p')`, then compose in each factor. -/
lemma dgCompMap_tensor (X Y Z : C × D) (p q p' q' n n' m : ℤ)
    (h : p + q = n) (h' : p' + q' = n') (hm : n + n' = m) :
    (ιTensorObj (dgHomComplex R X.1 Y.1) (dgHomComplex R X.2 Y.2) p q n h ⊗ₘ
        ιTensorObj (dgHomComplex R Y.1 Z.1) (dgHomComplex R Y.2 Z.2) p' q' n' h') ≫
      dgCompMap R X Y Z n n' m hm =
    (q * p').negOnePow • (tensorμ _ _ _ _ ≫
      (dgCompMap R X.1 Y.1 Z.1 p p' (p + p') rfl ⊗ₘ dgCompMap R X.2 Y.2 Z.2 q q' (q + q') rfl) ≫
        ιTensorObj (dgHomComplex R X.1 Z.1) (dgHomComplex R X.2 Z.2) (p + p') (q + q') m
          (by omega)) := by
  subst h h'
  rw [dgCompMap_def, eComp_tensor_eq, HomologicalComplex.comp_f]
  simp only [eHom_tensor_eq]
  rw [ι_tensorμ_assoc, Linear.units_smul_comp, Category.assoc, Category.assoc,
    tensorHom_eq_mapBifunctorMap, ι_mapBifunctorMap, curriedTensor_map_app, curriedTensor_obj_map,
    ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc, ← dgCompMap_def, ← dgCompMap_def]

/-- **Composition in a tensor product of differential graded categories.** For homogeneous
morphisms `f`, `g`, `f'`, `g'` of degrees `p`, `q`, `p'`, `q'`, the composite of `f ⊗ g` and
`f' ⊗ g'` is `dgComp f f' ⊗ dgComp g g'` up to the Koszul sign `(-1) ^ (q * p')` of moving `g`
past `f'`. -/
@[simp]
theorem dgComp_dgTensorHom {X Y Z : C × D} {p q p' q' n n' m : ℤ} (f : DGHom R p X.1 Y.1)
    (g : DGHom R q X.2 Y.2) (f' : DGHom R p' Y.1 Z.1) (g' : DGHom R q' Y.2 Z.2)
    (h : p + q = n) (h' : p' + q' = n') (hm : n + n' = m) :
    dgComp R (dgTensorHom R f g h) (dgTensorHom R f' g' h') hm =
      (q * p').negOnePow •
        dgTensorHom R (dgComp R f f' rfl) (dgComp R g g' rfl) (by omega) := by
  subst h h'
  have key := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (dgCompMap_tensor R X Y Z p q p' q' (p + q) (p' + q') m rfl rfl hm))
    ((f ⊗ₜ g) ⊗ₜ (f' ⊗ₜ g'))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply] at key
  -- The evaluation lemmas of `ModuleCat` are stated for `ConcreteCategory.hom` on the carrier
  -- `↑(M ⊗ N)`, which the elements of `key` match only after unfolding.
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.MonoidalCategory.tensorμ_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, dgCompMap_tmul, dgCompMap_tmul,
    dgCompMap_tmul] at key
  rw [dgTensorHom_def, dgTensorHom_def, dgTensorHom_def]
  exact key

/-- The identity of an object of the tensor product of two differential graded categories is the
tensor product of the identities of its two components. -/
theorem dgId_tensor (X : C × D) :
    dgId R X = dgTensorHom R (dgId R X.1) (dgId R X.2) (add_zero 0) := by
  rw [dgId_def, eId_tensor_eq, HomologicalComplex.comp_f, leftUnitor_inv_f,
    leftUnitor'_inv, Category.assoc, Category.assoc, tensorHom_eq_mapBifunctorMap,
    ι_mapBifunctorMap]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, curriedTensor_map_app,
    curriedTensor_obj_map, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  rw [dgTensorHom_def, dgId_def, dgId_def]
  -- The two whiskerings act on the pure tensor by definition
  -- (`ModuleCat.MonoidalCategory.whiskerRight_apply` and `whiskerLeft_apply` are `rfl`); they do
  -- not fire as rewrites because the carrier of the tensor product is spelled differently.
  rfl

end MathlibExt.DGSource
