/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModelAtCardinal
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModelProperness

/-!
# Two explicit model dictionaries and the original given I/K factor clients

These clients keep an existing level model and the newly constructed model
in distinct carrier contexts. They compose both given replacement functions,
recover the original factor maps after carrier transport, and compare the
actual I-right maps in both dictionaries. The candidate right-class law is
explicit; this is a general client of recognition, not a native recognition
proof.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalGeneratedModelClients

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteColimits C]
  (I K W : MorphismProperty C)
  (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = K.rlp ⊓ W)
  (hAcyclic : K.rlp.llp ≤ W)
  (givenI : FunctorialFactorizationData I.rlp.llp I.rlp)
  (givenK : FunctorialFactorizationData K.rlp.llp K.rlp)

local notation "M" =>
  OriginalGeneratedModel.modelCategory I K W hW hRight hAcyclic givenI givenK

/-- The generic client supplies only the two original records and recognition laws. -/
example : OriginalGeneratedModel.RecognitionData I W :=
  OriginalGeneratedModel.recognition I K W hW hRight hAcyclic givenI givenK

example :
    (OriginalGeneratedModel.recognition I K W hW hRight hAcyclic givenI givenK).givenI =
      givenI :=
  OriginalGeneratedModel.recognition_givenI I K W hW hRight hAcyclic givenI givenK

example :
    (OriginalGeneratedModel.recognition I K W hW hRight hAcyclic givenI givenK).givenK =
      givenK :=
  OriginalGeneratedModel.recognition_givenK I K W hW hRight hAcyclic givenI givenK

example : K.rlp.llp = I.rlp.llp ⊓ W :=
  OriginalGeneratedModel.left_class_eq I K W hW hRight hAcyclic givenK

example (level : ModelCategory C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (hWeak : level.categoryWithWeakEquivalences.weakEquivalences ≤ W) :
    (OriginalGeneratedModel.levelToConstructedAdjunction
      I K W hW hRight hAcyclic givenI givenK level).IsQuillenAdjunction :=
  OriginalGeneratedModel.levelToConstructedAdjunction_isQuillen
    I K W hW hRight hAcyclic givenI givenK level hCof hWeak

example (level : ModelCategory C)
    (X : ExplicitModelIdentity.Carrier level) (Y : ExplicitModelIdentity.Carrier M)
    (f : (ExplicitModelIdentity.comparison level M).obj X ⟶ Y) :
    ((ExplicitModelIdentity.identityAdjunction level M).homEquiv X Y f).hom = f.hom :=
  ExplicitModelIdentity.identityAdjunction_homEquiv_hom level M X Y f

example (level : ModelCategory C)
    (X : ExplicitModelIdentity.Carrier level) (Y : ExplicitModelIdentity.Carrier M)
    (f : X ⟶ (ExplicitModelIdentity.comparison M level).obj Y) :
    (((ExplicitModelIdentity.identityAdjunction level M).homEquiv X Y).symm f).hom =
      f.hom :=
  ExplicitModelIdentity.identityAdjunction_homEquiv_symm_hom level M X Y f

example (F : Arrow (ExplicitModelIdentity.Carrier M)) :
    ((OriginalGeneratedModel.cofibrantFactorizationOnCarrier
      I K W hW hRight hAcyclic givenI givenK).p.app F).hom =
        givenI.p.app ((ExplicitModelIdentity.toBase M).mapArrow.obj F) :=
  OriginalGeneratedModel.cofibrantFactorizationOnCarrier_p
    I K W hW hRight hAcyclic givenI givenK F

example (F : Arrow (ExplicitModelIdentity.Carrier M)) :
    ((OriginalGeneratedModel.fibrantFactorizationOnCarrier
      I K W hW hRight hAcyclic givenI givenK).i.app F).hom =
        givenK.i.app ((ExplicitModelIdentity.toBase M).mapArrow.obj F) :=
  OriginalGeneratedModel.fibrantFactorizationOnCarrier_i
    I K W hW hRight hAcyclic givenI givenK F

example (Z : C) (hI : IsInitial Z) (hT : IsTerminal Z)
    {X Y : C} (f : X ⟶ Y) :
    ((OriginalGeneratedModel.cofibrantReplacement
        I K W hW hRight hAcyclic givenI givenK Z hI).map f ≫
      (OriginalGeneratedModel.cofibrantReplacementProjection
        I K W hW hRight hAcyclic givenI givenK Z hI).app Y) ≫
      (OriginalGeneratedModel.fibrantReplacementUnit
        I K W hW hRight hAcyclic givenI givenK Z hT).app Y =
      (OriginalGeneratedModel.cofibrantReplacementProjection
        I K W hW hRight hAcyclic givenI givenK Z hI).app X ≫
        (f ≫ (OriginalGeneratedModel.fibrantReplacementUnit
          I K W hW hRight hAcyclic givenI givenK Z hT).app Y) := by
  rw [OriginalGeneratedModel.cofibrantReplacementProjection_naturality,
    Category.assoc]

example (level : ModelCategory C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (F : Arrow C) :
    level.categoryWithWeakEquivalences.weakEquivalences (givenI.p.app F) ∧
      (M).categoryWithWeakEquivalences.weakEquivalences (givenI.p.app F) := by
  have hClasses := ExplicitModelIdentity.actual_trivialFibrations_eq level M hCof
  have hNew : ((M).categoryWithFibrations.fibrations ⊓
      (M).categoryWithWeakEquivalences.weakEquivalences) (givenI.p.app F) := by
    change (K.rlp ⊓ W) (givenI.p.app F)
    rw [← hRight]
    exact givenI.hp F
  have hOld : (level.categoryWithFibrations.fibrations ⊓
      level.categoryWithWeakEquivalences.weakEquivalences) (givenI.p.app F) := by
    rw [hClasses]
    exact hNew
  exact ⟨hOld.2, hNew.2⟩

example (Z : C) (hT : IsTerminal Z) (X : C) :
    letI : ModelCategory C := M
    IsFibrant ((OriginalGeneratedModel.fibrantReplacement
      I K W hW hRight hAcyclic givenI givenK Z hT).obj X) :=
  OriginalGeneratedModel.fibrantReplacement_isFibrant
    I K W hW hRight hAcyclic givenI givenK Z hT X

end HomotopicalAlgebra.OriginalGeneratedModelClients
