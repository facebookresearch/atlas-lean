/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Geometric realization of simplicial topological spaces

This file defines geometric realization of a simplicial object in `TopCat` as the coend

`X[n] × |Δ[n]|`.

It exposes the coend generators and universal property, the actual coproduct presentation of the
coend, and the natural isomorphism between the realization of a constant simplicial space and the
space itself.

This module contains only the realization core and its constant-object comparison.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Topology

open scoped Simplicial

namespace TopCat

/-- Geometric realization of a simplicial topological space, defined by the coend
`∫ⁿ X[n] × |Δ[n]|`. -/
noncomputable def simplicialRealization :
    SimplicialObject TopCat.{u} ⥤ TopCat.{u} :=
  (MonoidalCategory.externalProductBifunctorCurried
      SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj SimplexCategory.toTop ⋙
    Limits.coendFunctor SimplexCategory TopCat.{u}

namespace SimplicialRealization

/-- The canonical map from the degree-`n` summand into geometric realization. -/
noncomputable def ι (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) :
    X.obj (op n) ⊗ SimplexCategory.toTop.obj n ⟶ simplicialRealization.obj X :=
  Limits.coend.ι
    ((MonoidalCategory.externalProductBifunctorCurried
      SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
        SimplexCategory.toTop |>.obj X) n

/-- The defining coend relation for geometric realization. -/
theorem ι_condition (X : SimplicialObject TopCat.{u}) {m n : SimplexCategory}
    (α : m ⟶ n) :
    (X.map α.op ⊗ₘ 𝟙 (SimplexCategory.toTop.obj m)) ≫ ι X m =
      (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.map α) ≫ ι X n := by
  simpa only [ι, TopCat.simplicialRealization, Functor.comp_obj,
    Limits.coendFunctor_obj, Limits.coendFunctor, MonoidalCategory.tensorHom_def,
    MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id,
    Functor.flip_obj_obj, Functor.flip_obj_map, Functor.flip_map_app,
    externalProductBifunctorCurried_obj_obj_obj_obj,
    externalProductBifunctorCurried_obj_obj_map_app,
    externalProductBifunctorCurried_obj_obj_obj_map] using
    Limits.coend.condition
      ((MonoidalCategory.externalProductBifunctorCurried
        SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
          SimplexCategory.toTop |>.obj X) α

/-- Naturality of the canonical maps with respect to a map of simplicial spaces. -/
theorem ι_map {X Y : SimplicialObject TopCat.{u}} (f : X ⟶ Y)
    (n : SimplexCategory) :
    ι X n ≫ simplicialRealization.map f =
      (f.app (op n) ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫ ι Y n := by
  simpa only [ι, TopCat.simplicialRealization, Functor.comp_map,
    Limits.coendFunctor_map, Limits.coendFunctor, MonoidalCategory.tensorHom_def,
    MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id,
    Functor.flip_obj_obj, Functor.flip_obj_map, Functor.flip_map_app,
    externalProductBifunctorCurried_obj_obj_obj_obj,
    externalProductBifunctorCurried_map_app_app_app] using
    Limits.coend.ι_map
      ((MonoidalCategory.externalProductBifunctorCurried
        SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
          SimplexCategory.toTop |>.map f) n

/-- Define a map out of geometric realization from compatible maps on all degree summands. -/
noncomputable def desc {X : SimplicialObject TopCat.{u}} {Z : TopCat.{u}}
    (f : ∀ n : SimplexCategory,
      X.obj (op n) ⊗ SimplexCategory.toTop.obj n ⟶ Z)
    (hf : ∀ ⦃m n : SimplexCategory⦄ (α : m ⟶ n),
      (X.map α.op ⊗ₘ 𝟙 (SimplexCategory.toTop.obj m)) ≫ f m =
        (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.map α) ≫ f n) :
    simplicialRealization.obj X ⟶ Z :=
  Limits.coend.desc
      (F := ((MonoidalCategory.externalProductBifunctorCurried
        SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
          SimplexCategory.toTop).obj X) f (by
    intro m n α
    simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id,
      Functor.flip_obj_obj,
      Functor.flip_obj_map, Functor.flip_map_app,
      externalProductBifunctorCurried_obj_obj_obj_obj,
      externalProductBifunctorCurried_obj_obj_map_app,
      externalProductBifunctorCurried_obj_obj_obj_map] using hf α)

/-- A map defined by `desc` has the prescribed value on every canonical summand. -/
@[simp]
theorem ι_desc {X : SimplicialObject TopCat.{u}} {Z : TopCat.{u}}
    (f : ∀ n : SimplexCategory,
      X.obj (op n) ⊗ SimplexCategory.toTop.obj n ⟶ Z)
    (hf : ∀ ⦃m n : SimplexCategory⦄ (α : m ⟶ n),
      (X.map α.op ⊗ₘ 𝟙 (SimplexCategory.toTop.obj m)) ≫ f m =
        (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.map α) ≫ f n)
    (n : SimplexCategory) :
    ι X n ≫ desc f hf = f n := by
  simpa only [ι, desc, TopCat.simplicialRealization, Functor.comp_obj,
    Limits.coendFunctor_obj, Limits.coendFunctor, Functor.flip_obj_obj,
    externalProductBifunctorCurried_obj_obj_obj_obj] using
    Limits.coend.ι_desc
      (F := ((MonoidalCategory.externalProductBifunctorCurried
        SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
          SimplexCategory.toTop).obj X) f (by
      intro m n α
      simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
        MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id,
        Functor.flip_obj_obj,
        Functor.flip_obj_map, Functor.flip_map_app,
        externalProductBifunctorCurried_obj_obj_obj_obj,
        externalProductBifunctorCurried_obj_obj_map_app,
        externalProductBifunctorCurried_obj_obj_obj_map] using hf α) n

/-- Maps out of geometric realization are equal when they agree on every canonical summand. -/
@[ext]
theorem hom_ext {X : SimplicialObject TopCat.{u}} {Z : TopCat.{u}}
    {f g : simplicialRealization.obj X ⟶ Z}
    (h : ∀ n : SimplexCategory, ι X n ≫ f = ι X n ≫ g) : f = g := by
  apply Limits.coend.hom_ext
    (F := ((MonoidalCategory.externalProductBifunctorCurried
      SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
        SimplexCategory.toTop).obj X)
  intro n
  simpa only [ι, TopCat.simplicialRealization, Functor.comp_obj,
    Limits.coendFunctor_obj, Limits.coendFunctor, Functor.flip_obj_obj,
    externalProductBifunctorCurried_obj_obj_obj_obj] using h n

/-- The coproduct of the degreewise pieces in the standard coend presentation. -/
noncomputable abbrev presentation (X : SimplicialObject TopCat.{u}) : TopCat.{u} :=
  ∐ fun n : SimplexCategory => X.obj (op n) ⊗ SimplexCategory.toTop.obj n

/-- The canonical quotient from the coproduct presentation onto geometric realization. -/
noncomputable def presentationQuotient (X : SimplicialObject TopCat.{u}) :
    presentation X ⟶ simplicialRealization.obj X :=
  Sigma.desc (ι X)

/-- The presentation quotient restricts to the coend generator on each summand. -/
@[simp]
theorem presentationQuotient_ι (X : SimplicialObject TopCat.{u})
    (n : SimplexCategory) :
    Sigma.ι (fun n : SimplexCategory =>
      X.obj (op n) ⊗ SimplexCategory.toTop.obj n) n ≫ presentationQuotient X = ι X n := by
  apply Sigma.ι_comp_desc

/-- The canonical map from the actual coproduct presentation of the coend is a quotient map. -/
theorem presentationQuotient_isQuotientMap (X : SimplicialObject TopCat.{u}) :
    IsQuotientMap (presentationQuotient X) := by
  let F := ((MonoidalCategory.externalProductBifunctorCurried
    SimplexCategoryᵒᵖ SimplexCategory TopCat.{u}).flip.obj
      SimplexCategory.toTop).obj X
  let I := Limits.multispanIndexCoend F
  have hPresentation :
      presentationQuotient X = Limits.Multicoequalizer.sigmaπ I := by
    apply Sigma.hom_ext
    intro n
    rw [presentationQuotient_ι]
    change Limits.Multicoequalizer.π I n =
      Sigma.ι I.right n ≫ Limits.Multicoequalizer.sigmaπ I
    exact (Limits.Multicoequalizer.ι_sigmaπ I n).symm
  rw [hPresentation]
  have hq : IsQuotientMap (coequalizer.π I.fstSigmaMap I.sndSigmaMap) :=
    TopCat.isQuotientMap_of_isColimit_cofork
      (coequalizer.cofork I.fstSigmaMap I.sndSigmaMap)
      (colimit.isColimit (parallelPair I.fstSigmaMap I.sndSigmaMap))
  have hi : IsQuotientMap (Limits.Multicoequalizer.isoCoequalizer I).inv :=
    (TopCat.homeoOfIso (Limits.Multicoequalizer.isoCoequalizer I).symm).isQuotientMap
  rw [Limits.Multicoequalizer.sigmaπ]
  change IsQuotientMap
    (⇑(Limits.Multicoequalizer.isoCoequalizer I).inv ∘
      ⇑(coequalizer.π I.fstSigmaMap I.sndSigmaMap))
  exact hi.comp hq

/-- Realization of constant simplicial spaces is naturally isomorphic to the identity functor. -/
noncomputable def constNatIso :
    SimplicialObject.const TopCat.{u} ⋙ simplicialRealization ≅ 𝟭 TopCat.{u} := by
  let projection : ∀ X : TopCat.{u},
      simplicialRealization.obj ((SimplicialObject.const TopCat).obj X) ⟶ X :=
    fun X =>
      desc (fun _ => CartesianMonoidalCategory.fst _ _) (by
        intro m n α
        simpa using
          (CartesianMonoidalCategory.tensorHom_fst
            (𝟙 X) (SimplexCategory.toTop.map α)).symm)
  let sectionMap : ∀ X : TopCat.{u},
      X ⟶ simplicialRealization.obj ((SimplicialObject.const TopCat).obj X) :=
    fun X =>
      CartesianMonoidalCategory.lift (𝟙 X)
          (TopCat.const (default : SimplexCategory.toTop.obj ⦋0⦌)) ≫
        ι ((SimplicialObject.const TopCat).obj X) ⦋0⦌
  have projection_section : ∀ X : TopCat.{u},
      projection X ≫ sectionMap X =
        𝟙 (simplicialRealization.obj ((SimplicialObject.const TopCat).obj X)) := by
    intro X
    apply hom_ext
    intro n
    rw [← Category.assoc, ι_desc]
    let α : n ⟶ ⦋0⦌ := default
    have hmap :
        CartesianMonoidalCategory.fst X (SimplexCategory.toTop.obj n) ≫
            CartesianMonoidalCategory.lift (𝟙 X)
              (TopCat.const (default : SimplexCategory.toTop.obj ⦋0⦌)) =
          𝟙 X ⊗ₘ SimplexCategory.toTop.map α := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
          CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
      · ext x
        exact Subsingleton.elim _ _
    dsimp only [sectionMap]
    simp only [Functor.const_obj_obj, Category.comp_id] at hmap ⊢
    rw [← Category.assoc, hmap]
    have hcondition :=
      ι_condition ((SimplicialObject.const TopCat).obj X) α
    simpa only [Functor.const_obj_obj, Functor.const_obj_map,
      MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp] using hcondition.symm
  have section_projection : ∀ X : TopCat.{u},
      sectionMap X ≫ projection X = 𝟙 X := by
    intro X
    dsimp only [sectionMap, projection]
    rw [Category.assoc, ι_desc]
    simp
  have projection_naturality : ∀ {X Y : TopCat.{u}} (f : X ⟶ Y),
      simplicialRealization.map ((SimplicialObject.const TopCat).map f) ≫
          projection Y =
        projection X ≫ f := by
    intro X Y f
    apply hom_ext
    intro n
    rw [← Category.assoc, ι_map, Category.assoc, ι_desc,
      ← Category.assoc, ι_desc]
    exact CartesianMonoidalCategory.tensorHom_fst
      f (𝟙 (SimplexCategory.toTop.obj n))
  exact NatIso.ofComponents
    (fun X =>
      { hom := projection X
        inv := sectionMap X
        hom_inv_id := projection_section X
        inv_hom_id := section_projection X })
    (fun f => projection_naturality f)

/-- The component at `X` of the natural constant-realization isomorphism. -/
noncomputable abbrev constIso (X : TopCat.{u}) :
    simplicialRealization.obj ((SimplicialObject.const TopCat).obj X) ≅ X :=
  constNatIso.app X

/-- On each coend generator, the forward constant-realization isomorphism is first projection. -/
@[simp]
theorem ι_constIso_hom (X : TopCat.{u}) (n : SimplexCategory) :
    ι ((SimplicialObject.const TopCat).obj X) n ≫ (constIso X).hom =
      CartesianMonoidalCategory.fst X (SimplexCategory.toTop.obj n) := by
  simpa only [constIso, Iso.app, constNatIso, NatIso.ofComponents_hom_app,
    Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj] using
    (ι_desc (X := (SimplicialObject.const TopCat).obj X)
      (fun _ => CartesianMonoidalCategory.fst _ _)
      (by
        intro m n α
        simpa using
          (CartesianMonoidalCategory.tensorHom_fst
            (𝟙 X) (SimplexCategory.toTop.map α)).symm) n)

end SimplicialRealization

end TopCat
