/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.UnderCokernelSupport
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Abelian.CommSq
public import MathlibExt.CategoryTheory.Limits.Constructions.Under.ConnectedCocone

/-!
# Colimits of cochain carriers with nonnegative reduced terms

For a fixed source complex, consider under arrows whose cokernels are nonnegative.
A connected colimiting cocone of the target complexes lifts to this full subcategory
with the same target complex and legs. The source arrow comes from the common
composition of the original arrows with the cocone legs. This gives an embedding
of the chosen pushout into a common target when the carrier span is its pullback and the
first map into the target is monic.
-/

@[expose] public section

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (I : CochainComplex C ℤ)

/-- Arrows from the fixed source whose actual cokernels are nonnegative. -/
abbrev NonnegativeReducedCarrier :=
  (underCokernelNonnegativeProperty I).FullSubcategory

/-- Forget the distinguished arrow and retain its actual cochain target. -/
abbrev nonnegativeReducedCarrierForget : NonnegativeReducedCarrier I ⥤ CochainComplex C ℤ :=
  (underCokernelNonnegativeProperty I).ι ⋙ Under.forget I

section Connected

variable {J : Type w} [Category.{w'} J] [IsConnected J]

/-- A connected cocone of the targets lifts with the arrow determined by its legs. -/
def liftConnectedUnderCarrierCocone {D : J ⥤ Under I}
    (s : Cocone (D ⋙ Under.forget I)) : Cocone D :=
  liftConnectedUnderCocone I s

variable [HasColimitsOfShape J C]

/-- Lift the original connected target cocone using its own legs and the induced source arrow. -/
def liftNonnegativeReducedCarrierCocone {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) : Cocone D := by
  let t := liftConnectedUnderCarrierCocone I (D := D ⋙ (underCokernelNonnegativeProperty I).ι) s
  have ht : IsColimit t := isColimitOfReflects (Under.forget I) (by exact hs)
  exact
    { pt := ⟨t.pt, underCokernelNonnegativeProperty_of_isColimit I ht fun j => (D.obj j).property⟩
      ι.app j := ObjectProperty.homMk (t.ι.app j)
      ι.naturality _ _ f :=
        ObjectProperty.hom_ext (underCokernelNonnegativeProperty I) (t.ι.naturality f) }

/-- The literal carrier cocone of the lift is the original cocone. -/
@[simp]
theorem mapCocone_liftNonnegativeReducedCarrierCocone {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) :
    (nonnegativeReducedCarrierForget I).mapCocone (liftNonnegativeReducedCarrierCocone I hs) = s :=
  rfl

/-- Every original coaugmentation followed by its cocone leg is the lifted coaugmentation. -/
@[reassoc]
theorem comp_ι_eq_liftNonnegativeReducedCarrierCocone_hom
    {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) (j : J) :
    (D.obj j).obj.hom ≫ s.ι.app j = (liftNonnegativeReducedCarrierCocone I hs).pt.obj.hom :=
  Under.w ((liftNonnegativeReducedCarrierCocone I hs).ι.app j).hom

/-- The lifted cocone is colimiting in the full subcategory. -/
def isColimitLiftNonnegativeReducedCarrierCocone {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) :
    IsColimit (liftNonnegativeReducedCarrierCocone I hs) :=
  isColimitOfReflects (underCokernelNonnegativeProperty I).ι
    (isColimitOfReflects (Under.forget I) hs)

/-- The actual carrier forgetful functor creates connected colimits. -/
instance nonnegativeReducedCarrierForgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (nonnegativeReducedCarrierForget I) where
  CreatesColimit := createsColimitOfReflectsIso fun _ hs =>
    { liftedCocone := liftNonnegativeReducedCarrierCocone I hs
      validLift := eqToIso (mapCocone_liftNonnegativeReducedCarrierCocone I hs)
      makesColimit := isColimitLiftNonnegativeReducedCarrierCocone I hs }

/-- The support subcategory has connected colimits whenever the coefficient category does. -/
instance nonnegativeReducedCarrier_hasColimitsOfShape :
    HasColimitsOfShape J (NonnegativeReducedCarrier I) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (nonnegativeReducedCarrierForget I)

end Connected

/-- The literal pushout comparison into the common target is monic on whole carriers
when the input span is its actual carrier intersection. -/
theorem nonnegativeReducedCarrier_pushoutDesc_mono
    {L A B D : NonnegativeReducedCarrier I} {t : L ⟶ A} {l : L ⟶ B}
    {a : A ⟶ D} {b : B ⟶ D} (w : t ≫ a = l ≫ b)
    (h : IsPullback ((nonnegativeReducedCarrierForget I).map t)
      ((nonnegativeReducedCarrierForget I).map l)
      ((nonnegativeReducedCarrierForget I).map a)
      ((nonnegativeReducedCarrierForget I).map b))
    [Mono ((nonnegativeReducedCarrierForget I).map a)] :
    Mono ((nonnegativeReducedCarrierForget I).map (pushout.desc a b w)) := by
  let F := nonnegativeReducedCarrierForget I
  have hp := (IsPushout.of_hasPushout t l).map F
  refine hp.mono_of_isPullback_of_mono h (F.map (pushout.desc a b w)) ?_ ?_
  · rw [← F.map_comp, pushout.inl_desc]
  · rw [← F.map_comp, pushout.inr_desc]

end CochainComplex
