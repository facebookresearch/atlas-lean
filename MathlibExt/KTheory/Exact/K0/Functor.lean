/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.KTheory.Exact.K0.Basic

/-!
# Functoriality of K₀ for exact categories

An exact functor between exact categories induces an abelian group morphism on the
respective K₀ groups.

## Main definitions
* `AlgebraicKTheory.K0.map`

## Main results
* `AlgebraicKTheory.K0.map_id`
* `AlgebraicKTheory.K0.map_comp`
* `AlgebraicKTheory.K0.map_eq_of_iso`
* `AlgebraicKTheory.K0.map_comp_eq_comp_of_iso`
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {D' : Type u₄} [Category.{v₄} D'] [Preadditive D']
  [HasZeroObject D'] [HasBinaryBiproducts D'] [ExactCategory D']

/-- The abelian group morphism on K₀ induced by an exact functor -/
noncomputable def K0.map (F : C ⥤ D) [F.Additive] [F.IsExact] : K0 C →+ K0 D :=
  QuotientAddGroup.map _ _ (FreeAbelianGroup.map F.mapSkeleton.obj) (by
    unfold K0Rel
    rw [AddSubgroup.closure_le]
    rintro y ⟨S, hS, rfl⟩
    simp only [AddSubgroup.mem_comap, SetLike.mem_coe, map_sub,
      FreeAbelianGroup.map_of_apply, Functor.mapSkeleton_obj_toSkeleton]
    apply AddSubgroup.subset_closure
    exact ⟨S.map F, F.map_admissibleExact S hS, rfl⟩)

@[simp]
lemma K0.map_mk (F : C ⥤ D) [F.Additive] [F.IsExact] (X : C) :
    K0.map F (K0.mk X) = K0.mk (F.obj X) := by
  simp [K0.map, K0.mk, Functor.mapSkeleton_obj_toSkeleton]

@[simp]
lemma K0.map_id : K0.map (𝟭 C) = AddMonoidHom.id (K0 C) := by
  apply K0.hom_ext
  intro X
  simp

lemma K0.map_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    K0.map (F ⋙ G) = (K0.map G).comp (K0.map F) := by
  apply K0.hom_ext
  intro X
  simp

/-- If `F` and `G` are naturally isomorphic (additive and exact) functors, they induce the same
map on `K₀`. This follows because each component of the natural isomorphism is an isomorphism
of objects, hence identifies the corresponding `K₀`-classes via `K0.mk_congr_of_iso`. -/
theorem K0.map_eq_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (e : F ≅ G) : K0.map F = K0.map G := by
  apply K0.hom_ext
  intro X
  simp only [K0.map_mk]
  exact K0.mk_congr_of_iso (e.app X)

/-- Naturally isomorphic factorizations induce the same composite map on `K₀`. -/
theorem K0.map_comp_eq_comp_of_iso
    {F₁ : C ⥤ D} {G₁ : D ⥤ E} {F₂ : C ⥤ D'} {G₂ : D' ⥤ E}
    [F₁.Additive] [G₁.Additive] [F₂.Additive] [G₂.Additive]
    [F₁.IsExact] [G₁.IsExact] [F₂.IsExact] [G₂.IsExact]
    (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂) :
    (K0.map G₁).comp (K0.map F₁) = (K0.map G₂).comp (K0.map F₂) := by
  rw [← K0.map_comp F₁ G₁, ← K0.map_comp F₂ G₂]
  exact K0.map_eq_of_iso e

end AlgebraicKTheory
