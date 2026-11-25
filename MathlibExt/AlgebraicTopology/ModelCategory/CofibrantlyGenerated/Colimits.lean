/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Actual working-size colimits from generation data

The supplied original small-object dictionary gives working-size
coproducts. The original model gives finite coequalizers. Their actual
coproduct/coequalizer construction yields the colimits and full original
cocone universal properties, without local presentability.

These are explicit getters. A model category alone is not asserted to
have arbitrary working-size colimits, and no global chosen colimit or
new generation datum is installed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v uJ vJ
open CategoryTheory Limits

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {M : Type u} [Category.{v} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]


/-- The actual I small-object dictionary supplies its original working-size coproducts. -/
theorem hasCoproducts (d : CofibrantGenerationData M κ) : HasCoproducts.{w} M := by
  let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact SmallObject.hasCoproducts d.I κ

/-- Actual finite coequalizers and the stored coproduct dictionary supply all working colimits. -/
theorem hasColimitsOfSize (d : CofibrantGenerationData M κ) : HasColimitsOfSize.{w, w} M := by
  let _ : HasCoproducts.{w} M := d.hasCoproducts
  exact has_colimits_of_hasCoequalizers_and_coproducts

/-- The same original generation datum supplies every fixed working-size ordinal iteration. -/
theorem hasIterationOfShape (d : CofibrantGenerationData M κ)
    {T : Type w} [LinearOrder T] : HasIterationOfShape T M := by
  let _ : HasColimitsOfSize.{w, w} M := d.hasColimitsOfSize
  infer_instance

/-- A genuinely small original diagram category keeps its own original colimit shape. -/
theorem hasColimitsOfShape (d : CofibrantGenerationData M κ)
    {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{w} J] :
    HasColimitsOfShape J M := by
  let _ : HasColimitsOfSize.{w, w} M := d.hasColimitsOfSize
  exact hasColimitsOfShape_of_essentiallySmall J M

section ActualCocone

variable {J : Type w} [SmallCategory J]

/-- The actual original diagram uses the existing coproduct/coequalizer colimit cocone. -/
def colimitCocone (d : CofibrantGenerationData M κ) (F : J ⥤ M) : ColimitCocone F := by
  letI : HasCoproducts.{w} M := d.hasCoproducts
  exact colimitCoconeOfCoequalizerAndCoproduct F

/-- The whole original cocone is exactly the existing coproduct/coequalizer construction. -/
theorem colimitCocone_eq (d : CofibrantGenerationData M κ) (F : J ⥤ M) :
    letI : HasCoproducts.{w} M := d.hasCoproducts
    d.colimitCocone F = colimitCoconeOfCoequalizerAndCoproduct F := rfl

/-- Every actual original index action commutes with its selected cocone legs. -/
theorem colimitCocone_naturality (d : CofibrantGenerationData M κ) (F : J ⥤ M)
    {i j : J} (f : i ⟶ j) :
    F.map f ≫ (d.colimitCocone F).cocone.ι.app j =
      (d.colimitCocone F).cocone.ι.app i :=
  (d.colimitCocone F).cocone.w f

/-- The descender is the original selected cocone universal-property map. -/
def colimitDesc (d : CofibrantGenerationData M κ) (F : J ⥤ M)
    (s : Cocone F) : (d.colimitCocone F).cocone.pt ⟶ s.pt :=
  (d.colimitCocone F).isColimit.desc s

/-- The actual descender retains every original cocone equation. -/
theorem colimitDesc_fac (d : CofibrantGenerationData M κ) (F : J ⥤ M)
    (s : Cocone F) (j : J) :
    (d.colimitCocone F).cocone.ι.app j ≫ d.colimitDesc F s = s.ι.app j :=
  (d.colimitCocone F).isColimit.fac s j

/-- The original cocone legs determine its actual descender uniquely. -/
theorem colimitDesc_uniq (d : CofibrantGenerationData M κ) (F : J ⥤ M)
    (s : Cocone F) (f : (d.colimitCocone F).cocone.pt ⟶ s.pt)
    (hf : ∀ j : J, (d.colimitCocone F).cocone.ι.app j ≫ f = s.ι.app j) :
    f = d.colimitDesc F s :=
  (d.colimitCocone F).isColimit.uniq s f hf

/-- Whole functions out of the selected colimit retain extensionality on original index legs. -/
theorem colimitCocone_hom_ext (d : CofibrantGenerationData M κ) (F : J ⥤ M)
    {X : M} (f g : (d.colimitCocone F).cocone.pt ⟶ X)
    (hfg : ∀ j : J, (d.colimitCocone F).cocone.ι.app j ≫ f =
      (d.colimitCocone F).cocone.ι.app j ≫ g) : f = g :=
  (d.colimitCocone F).isColimit.hom_ext hfg

end ActualCocone

end HomotopicalAlgebra.CofibrantGenerationData
