/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization

/-!
# The two original projective factorization values

Both values use the returned generation data on the existing model and the
same input cardinal. Their complete computational fields are the original
free-family small-object construction; membership is the only conversion.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective
variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
  [ModelCategory M] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} D] [LocallySmall.{w} D] (d : CofibrantGenerationData M κ)

/-- The original projective I-factorization is the generic fixed-generation getter. -/
def cofibrantFactorizationData :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact (generationData (D := D) d).cofibrantFactorizationData

/-- The original projective J-factorization is the same generic getter at the input cardinal. -/
def fibrantFactorizationData :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact (generationData (D := D) d).fibrantFactorizationData

/-- The whole I middle functor remains the literal free-I small-object functor. -/
theorem cofibrantFactorizationData_Z :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ := freeI_eligible d
    (cofibrantFactorizationData (D := D) d).Z =
      (SmallObject.functorialFactorizationData (freeGenerators (D := D) d d.I) κ).Z := rfl

/-- The whole J middle functor remains the literal free-J small-object functor. -/
theorem fibrantFactorizationData_Z :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ := freeJ_eligible d
    (fibrantFactorizationData (D := D) d).Z =
      (SmallObject.functorialFactorizationData (freeGenerators (D := D) d d.J) κ).Z := rfl

/-- The entire I left transformation is the original free-family cellular inclusion. -/
theorem cofibrantFactorizationData_i :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ := freeI_eligible d
    (cofibrantFactorizationData (D := D) d).i =
      (SmallObject.functorialFactorizationData (freeGenerators (D := D) d d.I) κ).i := rfl

/-- The entire I right transformation is the original free-family projection. -/
theorem cofibrantFactorizationData_p :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ := freeI_eligible d
    (cofibrantFactorizationData (D := D) d).p =
      (SmallObject.functorialFactorizationData (freeGenerators (D := D) d d.I) κ).p := rfl

/-- The entire J left transformation is the original free-family cellular inclusion. -/
theorem fibrantFactorizationData_i :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ := freeJ_eligible d
    (fibrantFactorizationData (D := D) d).i =
      (SmallObject.functorialFactorizationData (freeGenerators (D := D) d d.J) κ).i := rfl

/-- The entire J right transformation is the original free-family projection. -/
theorem fibrantFactorizationData_p :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ := freeJ_eligible d
    (fibrantFactorizationData (D := D) d).p =
      (SmallObject.functorialFactorizationData (freeGenerators (D := D) d d.J) κ).p := rfl

/-- Every I middle object is the actual fixed-cardinal free-family endpoint. -/
theorem cofibrantFactorizationData_obj (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ := freeI_eligible d
    (cofibrantFactorizationData (D := D) d).Z.obj f =
      SmallObject.obj (freeGenerators (D := D) d d.I) κ f.hom := rfl

/-- Every J middle object is the actual fixed-cardinal free-family endpoint. -/
theorem fibrantFactorizationData_obj (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ := freeJ_eligible d
    (fibrantFactorizationData (D := D) d).Z.obj f =
      SmallObject.obj (freeGenerators (D := D) d d.J) κ f.hom := rfl

/-- Every I middle arrow is the original small-object map of the caller's full square. -/
theorem cofibrantFactorizationData_map {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ := freeI_eligible d
    (cofibrantFactorizationData (D := D) d).Z.map φ =
      SmallObject.objMap (freeGenerators (D := D) d d.I) κ φ := rfl

/-- Every J middle arrow is the original small-object map of the caller's full square. -/
theorem fibrantFactorizationData_map {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    letI : (freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ := freeJ_eligible d
    (fibrantFactorizationData (D := D) d).Z.map φ =
      SmallObject.objMap (freeGenerators (D := D) d d.J) κ φ := rfl

/-- Every original component retains the strict cofibrant factor equation. -/
theorem cofibrantFactorizationData_fac_app (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    ((cofibrantFactorizationData d).i.app f).app x ≫
      ((cofibrantFactorizationData d).p.app f).app x =
      f.hom.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact NatTrans.congr_app ((cofibrantFactorizationData d).fac_app) x

/-- Every original component retains cofibrant left-map naturality. -/
theorem cofibrantFactorizationData_i_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    φ.left.app x ≫ ((cofibrantFactorizationData d).i.app g).app x =
      ((cofibrantFactorizationData d).i.app f).app x ≫
      ((cofibrantFactorizationData d).Z.map φ).app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact NatTrans.congr_app ((cofibrantFactorizationData d).i.naturality φ) x

/-- Every original component retains cofibrant right-map naturality. -/
theorem cofibrantFactorizationData_p_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    ((cofibrantFactorizationData d).Z.map φ).app x ≫
      ((cofibrantFactorizationData d).p.app g).app x =
      ((cofibrantFactorizationData d).p.app f).app x ≫ φ.right.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact NatTrans.congr_app ((cofibrantFactorizationData d).p.naturality φ) x

/-- Every original component retains the strict fibrant factor equation. -/
theorem fibrantFactorizationData_fac_app (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    ((fibrantFactorizationData d).i.app f).app x ≫ ((fibrantFactorizationData d).p.app f).app x =
      f.hom.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact NatTrans.congr_app ((fibrantFactorizationData d).fac_app) x

/-- Every original component retains fibrant left-map naturality. -/
theorem fibrantFactorizationData_i_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    φ.left.app x ≫ ((fibrantFactorizationData d).i.app g).app x =
      ((fibrantFactorizationData d).i.app f).app x ≫
      ((fibrantFactorizationData d).Z.map φ).app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact NatTrans.congr_app ((fibrantFactorizationData d).i.naturality φ) x

/-- Every original component retains fibrant right-map naturality. -/
theorem fibrantFactorizationData_p_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    ((fibrantFactorizationData d).Z.map φ).app x ≫ ((fibrantFactorizationData d).p.app g).app x =
      ((fibrantFactorizationData d).p.app f).app x ≫ φ.right.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact NatTrans.congr_app ((fibrantFactorizationData d).p.naturality φ) x

end HomotopicalAlgebra.FunctorProjective
