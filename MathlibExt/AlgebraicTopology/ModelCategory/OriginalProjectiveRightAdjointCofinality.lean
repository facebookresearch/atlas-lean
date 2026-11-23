/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalProjectiveDerivedColimits
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Final

/-!
# Actual projective homotopy-colimit cofinality for right-adjoint indices

The index functor has its actual specified left adjoint. Whiskering that
same adjunction gives restriction as a left Quillen functor on the
original plain-category projective models. Its actual restriction of the
original whole Q diagram is therefore projectively cofibrant.

The original projective Q counit gives one common-source weak leg.
The other uses the comparison on the earned cofibrant restricted Q
diagram and the actual ordinary finality isomorphism of the index
adjunction. Both entire natural weak legs give the cofinality NatIso
after the original model localization.

Both original index categories, coefficient model, generating cardinal,
free families and replacement choices remain. No arbitrary final-functor
homotopy-cofinality or simplex-diagonal result is supplied as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w uJ vJ uK vK uC vC
open CategoryTheory Limits HomotopicalAlgebra Opposite
open CategoryTheory.Functor

namespace HomotopicalAlgebra.OriginalProjectiveRightAdjointCofinality

variable {J : Type uJ} [Category.{vJ} J] [Small.{w} J] [LocallySmall.{w} J]
  {K : Type uK} [Category.{vK} K] [Small.{w} K] [LocallySmall.{w} K]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {l : K ⥤ J} {u : J ⥤ K} (adj : l ⊣ u)


omit [ModelCategory C] [Small.{w} J] [LocallySmall.{w} J] [Small.{w} K] [LocallySmall.{w} K] in
/-- The actual specified index adjunction gives BOTH full restriction functions. -/
def restrictionAdjunction : ((whiskeringLeft J K C).obj u) ⊣ ((whiskeringLeft K J C).obj l) := adj.whiskerLeft C

/-- The same actual restriction adjunction is Quillen because its right restriction keeps BOTH original objectwise right
classes. -/
theorem restriction_isQuillen :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    (restrictionAdjunction (C := C) adj).IsQuillenAdjunction := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  have h := FunctorProjective.Restriction.preserves_right_classes_of_eqs
    (FunctorProjective.fibrations_eq (J := K) d)
    (FunctorProjective.fibrations_eq (J := J) d)
    (FunctorProjective.trivialFibrations_eq (J := K) d)
    (FunctorProjective.trivialFibrations_eq (J := J) d) l
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (adj := restrictionAdjunction (C := C) adj) h.1 h.2

include adj in
/-- Actual right-adjoint index restriction preserves every genuinely projectively cofibrant whole source diagram. -/
theorem restriction_cofibrant (F : K ⥤ C) :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    IsCofibrant F → IsCofibrant (u ⋙ F) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : (restrictionAdjunction (C := C) adj).IsQuillenAdjunction := restriction_isQuillen d adj
  intro hF
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := restrictionAdjunction (C := C) adj) hF

include adj in
/-- The actual original Q diagram remains projectively cofibrant after the earned right-adjoint restriction. -/
theorem restriction_Q_cofibrant (F : K ⥤ C) :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    IsCofibrant (u ⋙ (GeneratedFunctorialReplacements.Q
      (FunctorProjective.generationData (D := K) d)).obj F) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact restriction_cofibrant d adj _ (GeneratedFunctorialReplacements.Q_isCofibrant
    (FunctorProjective.generationData (D := K) d) F)

/-- The common source is the SAME whole original Q followed by the actual index restriction. -/
def restrictedQ : (K ⥤ C) ⥤ (J ⥤ C) := by
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := K) d) ⋙ ((whiskeringLeft J K C).obj u)

/-- The original Q counit retains its entire source-to-restriction transformation. -/
def toRestriction : restrictedQ d (u := u) ⟶ ((whiskeringLeft J K C).obj u) := by
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact whiskerRight (GeneratedFunctorialReplacements.counit
    (FunctorProjective.generationData (D := K) d)) ((whiskeringLeft J K C).obj u)

/-- The first common-source leg applies the actual original homotopy-colimit functor to the entire Q counit. -/
def toRestrictedHomotopyColimit :
    restrictedQ d (u := u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⟶
      ((whiskeringLeft J K C).obj u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d :=
  whiskerRight (toRestriction d (u := u)) (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d)

/-- Both original projective Q vertices and actual source homotopicality earn weakness of the entire first comparison
leg. -/
theorem toRestrictedHomotopyColimit_weak (F : K ⥤ C) :
    weakEquivalences C ((toRestrictedHomotopyColimit d (u := u)).app F) := by
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  have hq := GeneratedFunctorialReplacements.counit_weak
    (FunctorProjective.generationData (D := K) d) F
  rw [FunctorProjective.weakEquivalences_eq d] at hq
  apply OriginalProjectiveDerivedColimits.homotopyColimit_map_weak d ((toRestriction d (u := u)).app F)
  intro j
  exact hq (u.obj j)

/-- Actual ordinary finality from the SAME index adjunction supplies the other entire original common-source leg. -/
def toOriginalHomotopyColimit :
    restrictedQ d (u := u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⟶
      OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : HasColimitsOfShape K C := d.hasColimitsOfShape
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : u.Final := Functor.final_of_adjunction adj
  let Q := GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := K) d)
  exact whiskerLeft (restrictedQ d (u := u)) (OriginalProjectiveDerivedColimits.comparison (J := J) d) ≫
    (associator Q ((whiskeringLeft J K C).obj u) colim).hom ≫ whiskerLeft Q (Functor.Final.colimIso u).hom

/-- Earned restricted-Q cofibrancy and actual ordinary finality prove weakness of the SAME complete second comparison
leg. -/
theorem toOriginalHomotopyColimit_weak (F : K ⥤ C) :
    weakEquivalences C ((toOriginalHomotopyColimit d adj).app F) := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : HasColimitsOfShape K C := d.hasColimitsOfShape
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : u.Final := Functor.final_of_adjunction adj
  let Q := GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := K) d)
  have hF := restriction_Q_cofibrant d adj F
  have hq := OriginalProjectiveDerivedColimits.comparison_weak_of_cofibrant d (u ⋙ Q.obj F) hF
  change weakEquivalences C
    ((OriginalProjectiveDerivedColimits.comparison (J := J) d).app (u ⋙ Q.obj F) ≫
      (𝟙 _ ≫ (Functor.Final.colimIso u).hom.app (Q.obj F)))
  rw [Category.id_comp]
  exact (weakEquivalences C).comp_mem _ _ hq (mem_weakEquivalences _)

/-- The whole first original common-source leg gives its actual localized NatIso. -/
def toRestrictedHoIso :
    restrictedQ d (u := u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙
        toHomotopyCategory C ≅
      ((whiskeringLeft J K C).obj u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory
        C := by
  let τ := whiskerRight (toRestrictedHomotopyColimit d (u := u)) (toHomotopyCategory C)
  let (F : K ⥤ C) : IsIso (τ.app F) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (toRestrictedHomotopyColimit_weak d F)
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The whole second original common-source leg gives the other actual localized NatIso. -/
def toOriginalHoIso :
    restrictedQ d (u := u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙
        toHomotopyCategory C ≅
      OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙ toHomotopyCategory C := by
  let τ := whiskerRight (toOriginalHomotopyColimit d adj) (toHomotopyCategory C)
  let (F : K ⥤ C) : IsIso (τ.app F) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (toOriginalHomotopyColimit_weak d adj F)
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- BOTH actual original weak legs give homotopy-colimit cofinality on EVERY full source diagram and map. -/
def cofinalHoIso :
    ((whiskeringLeft J K C).obj u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C
      ≅
      OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙ toHomotopyCategory C :=
  (toRestrictedHoIso d (u := u)).symm ≪≫ toOriginalHoIso d adj

/-- The entire cofinality Iso preserves each original whole diagram map. -/
theorem cofinalHoIso_naturality {F G : K ⥤ C} (f : F ⟶ G) :
    (((whiskeringLeft J K C).obj u) ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory
      C).map f ≫
        (cofinalHoIso d adj).hom.app G =
      (cofinalHoIso d adj).hom.app F ≫
        (OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙ toHomotopyCategory C).map f :=
  (cofinalHoIso d adj).hom.naturality f

section Localized

local notation "HPJ" => toHomotopyCategory (J ⥤ C)
local notation "HPK" => toHomotopyCategory (K ⥤ C)
local notation "WPJ" => weakEquivalences (J ⥤ C)
local notation "WPK" => weakEquivalences (K ⥤ C)

/-- The actual objectwise weak classes invert the full original restriction functor. -/
private theorem restriction_inverts :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    (WPK).IsInvertedBy (((whiskeringLeft J K C).obj u) ⋙ HPJ) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  intro F G f hf
  rw [FunctorProjective.weakEquivalences_eq d] at hf
  apply Localization.inverts HPJ WPJ
  rw [FunctorProjective.weakEquivalences_eq d]
  intro j
  exact hf (u.obj j)

/-- The SAME actual full index restriction descends through the original projective weak localization. -/
def derivedRestriction :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    HomotopyCategory (K ⥤ C) ⥤ HomotopyCategory (J ⥤ C) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact Localization.lift (((whiskeringLeft J K C).obj u) ⋙ HPJ) (restriction_inverts d (u := u)) HPK

/-- Both original localization comparison maps retain the SAME whole index restriction. -/
def derivedRestrictionProjection :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    HPK ⋙ derivedRestriction d (u := u) ≅ ((whiskeringLeft J K C).obj u) ⋙ HPJ := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact Localization.fac (((whiskeringLeft J K C).obj u) ⋙ HPJ) (restriction_inverts d (u := u)) HPK

/-- The original projective Q-colimit functor inverts every original projective weak arrow after localization. -/
private theorem colimit_inverts :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    (WPJ).IsInvertedBy (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙
      toHomotopyCategory C) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  intro F G f hf
  rw [FunctorProjective.weakEquivalences_eq d] at hf
  exact Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
    (OriginalProjectiveDerivedColimits.homotopyColimit_map_weak d f hf)

/-- The SAME entire original projective Q-colimit descends as the actual source-derived colimit functor. -/
def derivedColimit :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    HomotopyCategory (J ⥤ C) ⥤ HomotopyCategory C := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact Localization.lift (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙
    toHomotopyCategory C) (colimit_inverts (J := J) d) HPJ

/-- Both original projection maps retain the SAME actual original projective Q-colimit. -/
def derivedColimitProjection :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    HPJ ⋙ derivedColimit (J := J) d ≅
      OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact Localization.fac (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙
    toHomotopyCategory C) (colimit_inverts (J := J) d) HPJ

/-- Every full composite projection preserves BOTH original restriction and Q-colimit comparison functions. -/
def compositeProjection :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    HPK ⋙ (derivedRestriction d (u := u) ⋙ derivedColimit (J := J) d) ≅
      ((whiskeringLeft J K C).obj u) ⋙
        OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact (associator HPK (derivedRestriction d (u := u)) (derivedColimit (J := J) d)).symm ≪≫
    isoWhiskerRight (derivedRestrictionProjection d (u := u)) (derivedColimit (J := J) d) ≪≫
      associator ((whiskeringLeft J K C).obj u) HPJ (derivedColimit (J := J) d) ≪≫
        isoWhiskerLeft ((whiskeringLeft J K C).obj u) (derivedColimitProjection (J := J) d)

/-- BOTH actual original common-source weak legs give the full cofinality NatIso on EVERY object and arrow of projective
Ho. -/
def derivedCofinalIso :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    derivedRestriction d (u := u) ⋙ derivedColimit (J := J) d ≅ derivedColimit (J := K) d := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : Localization.Lifting HPK WPK
      (((whiskeringLeft J K C).obj u) ⋙
        OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C)
      (derivedRestriction d (u := u) ⋙ derivedColimit (J := J) d) :=
    ⟨compositeProjection d (u := u)⟩
  let : Localization.Lifting HPK WPK
      (OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙ toHomotopyCategory C)
      (derivedColimit (J := K) d) := ⟨derivedColimitProjection (J := K) d⟩
  exact Localization.liftNatIso HPK WPK
    (((whiskeringLeft J K C).obj u) ⋙
      OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C)
    (OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙ toHomotopyCategory C)
    (derivedRestriction d (u := u) ⋙ derivedColimit (J := J) d) (derivedColimit (J := K) d)
    (cofinalHoIso d adj)

/-- Every original full projective-Ho morphism preserves the SAME actual source-derived cofinality comparison. -/
theorem derivedCofinalIso_naturality :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    ∀ {F G : HomotopyCategory (K ⥤ C)} (f : F ⟶ G),
      (derivedRestriction d (u := u) ⋙ derivedColimit (J := J) d).map f ≫
          (derivedCofinalIso d adj).hom.app G =
        (derivedCofinalIso d adj).hom.app F ≫ (derivedColimit (J := K) d).map f := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  intro F G f
  exact (derivedCofinalIso d adj).hom.naturality f

end Localized

end HomotopicalAlgebra.OriginalProjectiveRightAdjointCofinality
