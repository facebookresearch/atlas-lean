/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.RealizationSingular
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWH
public import Mathlib.CategoryTheory.IsConnected

/-!
# Singular homology of categorical classifying spaces

The singular homology of the native CGWH classifying space of a category is
canonically isomorphic to the simplicial homology of its nerve.  The
comparison is natural in the category and universe-polymorphic.

We also record that the nerve of a connected category is connected.  This
file makes no degree-one Hurewicz, fundamental-group, finite-BGL, kernel,
plus-construction, or `Q = +` claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory

/-- The nerve of a connected category is connected as a simplicial set. -/
theorem nerve_isConnected_of_category_isConnected
    {C : Type u} [Category.{v} C] [IsConnected C] :
    (nerve C).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        let componentOf : C → SSet.π₀ (nerve C) :=
          fun X ↦ SSet.π₀.mk (nerveEquiv.symm X)
        have componentOf_eq : ∀ X Y : C, ∀ f : X ⟶ Y,
            componentOf X = componentOf Y := by
          intro X Y f
          exact SSet.π₀.sound (nerve.edgeMk f)
        calc
          SSet.π₀.mk x = componentOf (nerveEquiv x) :=
            congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply x).symm
          _ = componentOf (nerveEquiv y) :=
            constant_of_preserves_morphisms
              componentOf componentOf_eq _ _
          _ = SSet.π₀.mk y :=
            congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply y)
  · exact ⟨nerveEquiv.symm (Classical.arbitrary C)⟩

/-- Integral singular homology of a native CGWH classifying space, compared
with simplicial homology of the categorical nerve. -/
noncomputable def classifyingSpaceCGWHSingularIntegralHomologyIso
    (C : Type u) [Category.{v} C] (n : ℕ) :
    AlgebraicTopology.singularIntegralHomology n
        (CGWH.cgwhToTop.obj
          (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))) ≅
      (nerve C).homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{max u v}) n :=
  (AlgebraicTopology.singularIntegralHomologyFunctor n).mapIso
      ((classifyingSpaceCGWHToTopIso.{w, v, u}).app (Cat.of C)) ≪≫
    (SSet.realizationSingularHomologyIso
      AlgebraicTopology.singularIntegralCoefficients (nerve C) n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The classifying-space singular/simplicial homology comparison is natural,
in the map-first orientation. -/
@[reassoc]
theorem classifyingSpaceCGWHSingularIntegralHomologyIso_hom_naturality
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor n).map
          (CGWH.cgwhToTop.map
            (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)) ≫
        (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} D n).hom =
      (classifyingSpaceCGWHSingularIntegralHomologyIso.{w} C n).hom ≫
        SSet.homologyMap (nerveMap F)
          AlgebraicTopology.singularIntegralCoefficients n := by
  let A : AddCommGrpCat.{max u v} :=
    AlgebraicTopology.singularIntegralCoefficients
  let H := AlgebraicTopology.singularIntegralHomologyFunctor n
  let f := nerveMap F
  let fTop := SSet.toTop.map f
  let fCGWH := CGWH.cgwhToTop.map
    (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)
  let iC := (classifyingSpaceCGWHToTopIso.{w, v, u}).app (Cat.of C)
  let iD := (classifyingSpaceCGWHToTopIso.{w, v, u}).app (Cat.of D)
  let rC := SSet.realizationSingularHomologyIso A (nerve C) n
  let rD := SSet.realizationSingularHomologyIso A (nerve D) n
  have hTop : fCGWH ≫ iD.hom = iC.hom ≫ fTop := by
    simpa only [fCGWH, iD, iC, fTop, f, Functor.comp_map,
      Iso.app_hom, nerveFunctor, Functor.toCatHom] using
      (classifyingSpaceCGWHToTopIso.{w, v, u}).hom.naturality F.toCatHom
  have hMap : H.map fCGWH ≫ H.map iD.hom =
      H.map iC.hom ≫ H.map fTop := by
    have h := congrArg H.map hTop
    simpa only [H.map_comp] using h
  have hReal : H.map fTop ≫ rD.inv =
      rC.inv ≫ SSet.homologyMap f A n := by
    have h := SSet.realizationSingularHomologyIso_hom_naturality A f n
    change SSet.homologyMap f A n ≫ rD.hom =
      rC.hom ≫ H.map fTop at h
    calc
      H.map fTop ≫ rD.inv =
          (rC.inv ≫ rC.hom) ≫ H.map fTop ≫ rD.inv := by simp
      _ = rC.inv ≫ (rC.hom ≫ H.map fTop) ≫ rD.inv := by
        simp only [Category.assoc]
      _ = rC.inv ≫ (SSet.homologyMap f A n ≫ rD.hom) ≫
          rD.inv := by rw [h]
      _ = rC.inv ≫ SSet.homologyMap f A n := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change H.map fCGWH ≫ (H.map iD.hom ≫ rD.inv) =
    (H.map iC.hom ≫ rC.inv) ≫ SSet.homologyMap f A n
  calc
    H.map fCGWH ≫ (H.map iD.hom ≫ rD.inv) =
        (H.map fCGWH ≫ H.map iD.hom) ≫ rD.inv := by
          simp only [Category.assoc]
    _ = (H.map iC.hom ≫ H.map fTop) ≫ rD.inv := by rw [hMap]
    _ = H.map iC.hom ≫ (H.map fTop ≫ rD.inv) := by
      simp only [Category.assoc]
    _ = H.map iC.hom ≫
        (rC.inv ≫ SSet.homologyMap f A n) := by rw [hReal]
    _ = (H.map iC.hom ≫ rC.inv) ≫
        SSet.homologyMap f A n := by simp only [Category.assoc]

end CategoryTheory

end
