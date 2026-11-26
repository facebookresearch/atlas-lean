/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
import Mathlib.CategoryTheory.Discrete.Basic

/-!# Original diagram cocones and universal properties from actual generation data -/
set_option autoImplicit false
noncomputable section
universe w u v uJ vJ
open CategoryTheory Limits HomotopicalAlgebra

namespace MathlibExtTest.CofibrantGenerationColimits

variable {M : Type u} [Category.{v} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData M κ)

example : HasCoproducts.{w} M := d.hasCoproducts
example : HasColimitsOfSize.{w, w} M := d.hasColimitsOfSize

example {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{w} J] :
    HasColimitsOfShape J M := d.hasColimitsOfShape

example : HasIterationOfShape κ.ord.ToType M := d.hasIterationOfShape

section OriginalDiagram

variable {J : Type w} [SmallCategory J] (F : J ⥤ M)

example : ColimitCocone F := d.colimitCocone F

example : letI : HasCoproducts.{w} M := d.hasCoproducts
    d.colimitCocone F = colimitCoconeOfCoequalizerAndCoproduct F :=
  d.colimitCocone_eq F

example {i j : J} (f : i ⟶ j) :
    F.map f ≫ (d.colimitCocone F).cocone.ι.app j = (d.colimitCocone F).cocone.ι.app i :=
  d.colimitCocone_naturality F f

example (s : Cocone F) :
    (d.colimitCocone F).cocone.pt ⟶ s.pt := d.colimitDesc F s

example (s : Cocone F) (j : J) :
    (d.colimitCocone F).cocone.ι.app j ≫ d.colimitDesc F s = s.ι.app j :=
  d.colimitDesc_fac F s j

example (s : Cocone F) (f : (d.colimitCocone F).cocone.pt ⟶ s.pt)
    (hf : ∀ j : J, (d.colimitCocone F).cocone.ι.app j ≫ f = s.ι.app j) :
    f = d.colimitDesc F s :=
  d.colimitDesc_uniq F s f hf

example {X : M} (f g : (d.colimitCocone F).cocone.pt ⟶ X)
    (hfg : ∀ j : J, (d.colimitCocone F).cocone.ι.app j ≫ f =
      (d.colimitCocone F).cocone.ι.app j ≫ g) : f = g :=
  d.colimitCocone_hom_ext F f g hfg

end OriginalDiagram

section EmptyDiagram

example (F : Discrete (ULift.{w} PEmpty) ⥤ M) :
    letI : HasCoproducts.{w} M := d.hasCoproducts
    ColimitCocone F := d.colimitCocone F

end EmptyDiagram

section InfiniteDiagram

example (F : Discrete (ULift.{w} ℕ) ⥤ M) :
    letI : HasCoproducts.{w} M := d.hasCoproducts
    ColimitCocone F := d.colimitCocone F

end InfiniteDiagram

end MathlibExtTest.CofibrantGenerationColimits
