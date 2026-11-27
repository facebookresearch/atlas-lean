/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct

/-!
# Product corners and their image unions

The actual pushout-product of two monomorphisms is identified, over its
unchanged product target, with the union of their image subcomplexes.
This gives an image criterion in each degree for arbitrary monomorphisms,
not just for subcomplex inclusions.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace SSet

variable {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]

/-- The actual product corner is the union of the two image subcomplexes. -/
def pushoutProductUnionIso :
    (Arrow.mk i □ Arrow.mk j) ≅
      Arrow.mk ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι := by
  let eᵢ : Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
    Arrow.isoMk' i (Subcomplex.range i).ι
      (asIso (Subcomplex.toRange i)) (Iso.refl B) (by simp)
  let eⱼ : Arrow.mk j ≅ Arrow.mk (Subcomplex.range j).ι :=
    Arrow.isoMk' j (Subcomplex.range j).ι
      (asIso (Subcomplex.toRange j)) (Iso.refl L) (by simp)
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let sq₁ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    (Subcomplex.range i).ι j
  let E₀ := Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SSet.{u}) (f₁ := Arrow.mk i)
    (f₁' := Arrow.mk (Subcomplex.range i).ι) (f₂ := Arrow.mk j) sq₀ sq₁ eᵢ
  let E₁ := Functor.PushoutObjObj.ι_iso_of_iso_right
    (F := curriedTensor SSet.{u}) (f₁ := Arrow.mk (Subcomplex.range i).ι)
    (f₂ := Arrow.mk j) (f₂' := Arrow.mk (Subcomplex.range j).ι) sq₁
    (Subcomplex.unionProd.pushoutObjObj (Subcomplex.range i) (Subcomplex.range j)) eⱼ
  exact E₀ ≪≫ E₁

/-- The union comparison leaves the actual product target fixed. -/
@[simp]
lemma pushoutProductUnionIso_hom_right :
    (pushoutProductUnionIso i j).hom.right = 𝟙 (B ⊗ L) := by
  simp [pushoutProductUnionIso]

/-- The source comparison commutes strictly with the union inclusion. -/
@[reassoc (attr := simp)]
lemma pushoutProductUnionIso_hom_left_comp_ι :
    (pushoutProductUnionIso i j).hom.left ≫
        ((Subcomplex.range i).unionProd (Subcomplex.range j)).ι =
      (Arrow.mk i □ Arrow.mk j).hom := by
  simp

/-- A pair lies in the degreewise image of the actual pushout-product precisely
when at least one coordinate comes from its corresponding source. -/
lemma mem_range_pushoutProduct_iff (n : SimplexCategoryᵒᵖ) (b : B.obj n) (l : L.obj n) :
    (b, l) ∈ Set.range ((Arrow.mk i □ Arrow.mk j).hom.app n) ↔
      l ∈ Set.range (j.app n) ∨ b ∈ Set.range (i.app n) := by
  let U := (Subcomplex.range i).unionProd (Subcomplex.range j)
  let e : (Arrow.mk i □ Arrow.mk j).left ≅ (U : SSet.{u}) :=
    Arrow.leftFunc.mapIso (pushoutProductUnionIso i j)
  have left_comp : e.hom ≫ U.ι = (Arrow.mk i □ Arrow.mk j).hom :=
    pushoutProductUnionIso_hom_left_comp_ι i j
  have image_eq (x : (Arrow.mk i □ Arrow.mk j).left.obj n) :
      (e.hom.app n x).val = (Arrow.mk i □ Arrow.mk j).hom.app n x := by
    simpa only [SSet.comp_app, Subfunctor.ι_app, types_comp_apply, TypeCat.ofHom_apply] using!
      congrArg (fun f : (Arrow.mk i □ Arrow.mk j).left ⟶ B ⊗ L => f.app n x) left_comp
  have mem_union : (b, l) ∈ U.obj n ↔
      l ∈ Set.range (j.app n) ∨ b ∈ Set.range (i.app n) := by
    simpa only [Subfunctor.range_obj] using
      Subcomplex.mem_unionProd_iff (Subcomplex.range i) (Subcomplex.range j) (b, l)
  constructor
  · rintro ⟨x, hx⟩
    have hy := (e.hom.app n x).property
    rw [image_eq x, hx] at hy
    exact mem_union.mp hy
  · intro h
    let z : (U : SSet.{u}).obj n := ⟨(b, l), mem_union.mpr h⟩
    refine ⟨e.inv.app n z, ?_⟩
    rw [← image_eq]
    change (((e.inv ≫ e.hom).app n) z).val = (b, l)
    rw [e.inv_hom_id]
    rfl

end SSet
