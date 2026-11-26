/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneCoordinateData
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SimplicialPresheaf.OrderedJFS

/-- Reuse the actual PUBLIC same-universe site transport of the whole original scalar mapping
end. -/
def oneRawEndIso (A Z : Original.{u} 1) :
    innerHom A Z ≅ innerHom (oneOriginalEquivalence.{u}.functor.obj A)
      (oneOriginalEquivalence.{u}.functor.obj Z) :=
  innerHomTransportIso oneSiteEquivalence A Z

private theorem scalarTensorMap_transport {A B : Original.{u} 1}
    (f : A ⟶ B) (K : SSet.{u}) :
    oneOriginalEquivalence.{u}.functor.map ((scalarTensor.map f).app K) =
      (scalarTensor.map (oneOriginalEquivalence.{u}.functor.map f)).app K := rfl

-- Source naturality is a genuine consequence of the PUBLIC scalar characteristic, not private
-- uniqueness.
set_option backward.isDefEq.respectTransparency false in
private theorem oneRawEndIso_source {A B : Original.{u} 1} (f : A ⟶ B)
    (Z : Original.{u} 1) :
    innerHomPre f Z ≫ (oneRawEndIso A Z).hom =
      (oneRawEndIso B Z).hom ≫
        innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
          (oneOriginalEquivalence.{u}.functor.obj Z) := by
  let K := innerHom B Z
  let g := (scalarTensorHomEquiv B K Z).symm (𝟙 K)
  have hg : scalarTensorHomEquiv B K Z g = 𝟙 K := Equiv.apply_symm_apply _ _
  calc
    innerHomPre f Z ≫ (oneRawEndIso A Z).hom =
        scalarTensorHomEquiv A K Z ((scalarTensor.map f).app K ≫ g) ≫
          (oneRawEndIso A Z).hom := by
      rw [scalarTensorHomEquiv_source, hg, Category.id_comp]
    _ = scalarTensorHomEquiv (oneOriginalEquivalence.{u}.functor.obj A) K
        (oneOriginalEquivalence.{u}.functor.obj Z)
        (oneOriginalEquivalence.{u}.functor.map ((scalarTensor.map f).app K ≫ g)) :=
      innerHomTransportIso_scalar_map oneSiteEquivalence A Z K _
    _ = scalarTensorHomEquiv (oneOriginalEquivalence.{u}.functor.obj B) K
        (oneOriginalEquivalence.{u}.functor.obj Z)
        (oneOriginalEquivalence.{u}.functor.map g) ≫
          innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
            (oneOriginalEquivalence.{u}.functor.obj Z) := by
      rw [CategoryTheory.Functor.map_comp, scalarTensorMap_transport,
        scalarTensorHomEquiv_source]
    _ = (oneRawEndIso B Z).hom ≫
        innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
          (oneOriginalEquivalence.{u}.functor.obj Z) := by
      have h := innerHomTransportIso_scalar_map oneSiteEquivalence B Z K g
      have h' : (oneRawEndIso B Z).hom =
          scalarTensorHomEquiv (oneOriginalEquivalence.{u}.functor.obj B) K
            (oneOriginalEquivalence.{u}.functor.obj Z)
            (oneOriginalEquivalence.{u}.functor.map g) := by
        simpa only [oneRawEndIso, oneOriginalEquivalence, hg, Category.id_comp] using h
      exact congrArg (fun q => q ≫
        innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
          (oneOriginalEquivalence.{u}.functor.obj Z)) h'.symm

private theorem oneRawEndIso_source_inv {A B : Original.{u} 1} (f : A ⟶ B)
    (Z : Original.{u} 1) :
    innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
        (oneOriginalEquivalence.{u}.functor.obj Z) ≫ (oneRawEndIso A Z).inv =
      (oneRawEndIso B Z).inv ≫ innerHomPre f Z := by
  have h := congrArg (fun q =>
    (oneRawEndIso B Z).inv ≫ q ≫ (oneRawEndIso A Z).inv) (oneRawEndIso_source f Z)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h.symm

/-- BOTH original raw end precomposition endpoints and their native scalar maps are compared. -/
def oneMappingPrecompArrowIso {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1) :
    Arrow.mk (innerHomPre f Z) ≅
      Arrow.mk (innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
        (oneOriginalEquivalence.{u}.functor.obj Z)) :=
  Arrow.isoMk (oneRawEndIso B Z) (oneRawEndIso A Z) (oneRawEndIso_source f Z).symm

/-- All four actual original end Arrow projections are retained. -/
theorem oneMappingPrecompArrowIso_legs {A B : Original.{u} 1}
    (f : A ⟶ B) (Z : Original.{u} 1) :
    (oneMappingPrecompArrowIso f Z).hom.left = (oneRawEndIso B Z).hom ∧
    (oneMappingPrecompArrowIso f Z).hom.right = (oneRawEndIso A Z).hom ∧
    (oneMappingPrecompArrowIso f Z).inv.left = (oneRawEndIso B Z).inv ∧
    (oneMappingPrecompArrowIso f Z).inv.right = (oneRawEndIso A Z).inv :=
  ⟨rfl, rfl, rfl, rfl⟩


set_option backward.isDefEq.respectTransparency false in
private theorem oneRawEndIso_target (A : Original.{u} 1)
    {Z Z' : Original.{u} 1} (g : Z ⟶ Z') :
    innerHomPost A g ≫ (oneRawEndIso A Z').hom =
      (oneRawEndIso A Z).hom ≫
        innerHomPost (oneOriginalEquivalence.{u}.functor.obj A)
          (oneOriginalEquivalence.{u}.functor.map g) := by
  let H := innerHomFunctor.obj (op A)
  let E := transport oneSiteEquivalence
  let r := innerHomTransportRightIso oneSiteEquivalence A
  have hu := congrArg H.map (E.unitIso.hom.naturality g)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_map] at hu
  have hr := r.hom.naturality (E.functor.map g)
  simp only [CategoryTheory.Functor.comp_map] at hr
  change H.map g ≫ H.map (E.unitIso.hom.app Z') ≫ r.hom.app (E.functor.obj Z') =
    (H.map (E.unitIso.hom.app Z) ≫ r.hom.app (E.functor.obj Z)) ≫
      (innerHomFunctor.obj (op (E.functor.obj A))).map (E.functor.map g)
  rw [← Category.assoc, hu, Category.assoc, hr, ← Category.assoc]

private theorem oneRawEndIso_innerOperator (A Z : Original.{u} 1)
    {n m : SimplexCategoryᵒᵖ} (theta : n ⟶ m) :
    (innerHom A Z).map theta ≫ (oneRawEndIso A Z).hom.app m =
      (oneRawEndIso A Z).hom.app n ≫
        (innerHom (oneOriginalEquivalence.{u}.functor.obj A)
          (oneOriginalEquivalence.{u}.functor.obj Z)).map theta ∧
    (innerHom (oneOriginalEquivalence.{u}.functor.obj A)
          (oneOriginalEquivalence.{u}.functor.obj Z)).map theta ≫
      (oneRawEndIso A Z).inv.app m =
        (oneRawEndIso A Z).inv.app n ≫ (innerHom A Z).map theta :=
  ⟨(oneRawEndIso A Z).hom.naturality theta, (oneRawEndIso A Z).inv.naturality theta⟩


end SimplicialPresheaf.OrderedJFS
