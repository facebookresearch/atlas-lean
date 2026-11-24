/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence

/-! # Full original chosen derived-functor clients -/

public section
noncomputable section
universe u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅
open CategoryTheory Functor HomotopicalAlgebra
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace DerivedFunctorFullClients

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
  {F : Type u₄} [Category.{v₄} F] [ModelCategory F]
  {G : Type u₅} [Category.{v₅} G] [ModelCategory G]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]
  {M : D ⥤ E} {S : E ⥤ D} (b : M ⊣ S) [b.IsQuillenAdjunction]
  {N : E ⥤ F} {T : F ⥤ E} (c : N ⊣ T) [c.IsQuillenAdjunction]
  {P : F ⥤ G} {U : G ⥤ F} (d : P ⊣ U) [d.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))
  (qE : GeneratedFunctorialReplacements.Data (C := E))
  (qF : GeneratedFunctorialReplacements.Data (C := F))
  (qG : GeneratedFunctorialReplacements.Data (C := G))

/-- Every actual original source arrow retains the same Q map and left map. -/
theorem originalLeftMaps {X Y : C} (f : X ⟶ Y) :
    (left a qC).map ((projection C).map f) = (projection D).map (L.map (qC.Q.map f)) := left_map a qC f

/-- Every actual right arrow retains the same chosen R map. -/
theorem originalRightMaps {X Y : D} (f : X ⟶ Y) :
    (right a qD).map ((projection D).map f) = (projection C).map (R.map (qD.R.map f)) := right_map a qD f

/-- The whole original chosen left universal property is proved. -/
theorem wholeLeftDerived : (left a qC).IsLeftDerivedFunctor (leftComparison a qC) (weakEquivalences C) :=
  leftIsDerived a qC

/-- The full right universal property holds on the original weak localization. -/
theorem wholeRightDerived : (right a qD).IsRightDerivedFunctor (rightComparison a qD) (weakEquivalences D) :=
  rightIsDerived a qD

/-- The compositor keeps every original intermediate q map. -/
theorem originalLeftCompositor (X : C) :
    (leftCompositionIso a b qC qD).hom.app ((projection C).obj X) =
      (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) := leftCompositionIso_app a b qC qD X

/-- The right compositor keeps the actual intermediate r map. -/
theorem originalRightCompositor (Y : E) :
    (rightCompositionIso a b qD qE).hom.app ((projection E).obj Y) =
      (projection C).map (R.map (qD.r.app (S.obj (qE.R.obj Y)))) := rightCompositionIso_app a b qD qE Y

/-- Both entire left inverse equations hold as natural transformations. -/
theorem leftBothInverses :
    (leftCompositionIso a b qC qD).hom ≫ (leftCompositionIso a b qC qD).inv = 𝟙 _ ∧
      (leftCompositionIso a b qC qD).inv ≫ (leftCompositionIso a b qC qD).hom = 𝟙 _ :=
  ⟨(leftCompositionIso a b qC qD).hom_inv_id, (leftCompositionIso a b qC qD).inv_hom_id⟩

/-- Both entire right inverse transformations retain the same functors. -/
theorem rightBothInverses :
    (rightCompositionIso a b qD qE).hom ≫ (rightCompositionIso a b qD qE).inv = 𝟙 _ ∧
      (rightCompositionIso a b qD qE).inv ≫ (rightCompositionIso a b qD qE).hom = 𝟙 _ :=
  ⟨(rightCompositionIso a b qD qE).hom_inv_id, (rightCompositionIso a b qD qE).inv_hom_id⟩

/-- Both left comparison transformations are natural on arbitrary original localization arrows. -/
theorem leftFullNaturality {X Y : (weakEquivalences C).Localization} (f : X ⟶ Y) :
    (left a qC ⋙ left b qD).map f ≫ (leftCompositionIso a b qC qD).hom.app Y =
        (leftCompositionIso a b qC qD).hom.app X ≫ (left (a.comp b) qC).map f ∧
      (left (a.comp b) qC).map f ≫ (leftCompositionIso a b qC qD).inv.app Y =
        (leftCompositionIso a b qC qD).inv.app X ≫ (left a qC ⋙ left b qD).map f :=
  ⟨(leftCompositionIso a b qC qD).hom.naturality f, (leftCompositionIso a b qC qD).inv.naturality f⟩

/-- The entire actual left associativity square, with all original whiskers. -/
theorem fullLeftAssociativity :
    whiskerRight (leftCompositionIso a b qC qD).hom (left c qE) ≫
        (leftCompositionIso (a.comp b) c qC qE).hom =
      (Functor.associator (left a qC) (left b qD) (left c qE)).hom ≫
        whiskerLeft (left a qC) (leftCompositionIso b c qD qE).hom ≫
          (leftCompositionIso a (b.comp c) qC qD).hom := left_associativity a b c qC qD qE

/-- The full original right associativity diagram. -/
theorem fullRightAssociativity :
    (rightCompositionIso (a.comp b) c qE qF).hom ≫
        whiskerLeft (right c qF) (rightCompositionIso a b qD qE).hom =
      (rightCompositionIso a (b.comp c) qD qF).hom ≫
        whiskerRight (rightCompositionIso b c qE qF).hom (right a qD) ≫
          (Functor.associator (right c qF) (right b qE) (right a qD)).hom :=
  right_associativity a b c qD qE qF

/-- All original maps in the full four-functor left pentagon are preserved. -/
theorem fullLeftPentagon :
    whiskerRight (whiskerRight (leftCompositionIso a b qC qD).hom (left c qE)) (left d qF) ≫
        whiskerRight (leftCompositionIso (a.comp b) c qC qE).hom (left d qF) ≫
          (leftCompositionIso ((a.comp b).comp c) d qC qF).hom =
      (Functor.associator (left a qC ⋙ left b qD) (left c qE) (left d qF)).hom ≫
        (Functor.associator (left a qC) (left b qD) (left c qE ⋙ left d qF)).hom ≫
          whiskerLeft (left a qC) (whiskerLeft (left b qD) (leftCompositionIso c d qE qF).hom) ≫
            whiskerLeft (left a qC) (leftCompositionIso b (c.comp d) qD qE).hom ≫
              (leftCompositionIso a (b.comp (c.comp d)) qC qD).hom := left_pentagon a b c d qC qD qE qF

/-- The full right pentagon is an equality of complete natural transformations. -/
theorem fullRightPentagon :
    (rightCompositionIso ((a.comp b).comp c) d qF qG).hom ≫
        whiskerLeft (right d qG) (rightCompositionIso (a.comp b) c qE qF).hom ≫
          whiskerLeft (right d qG) (whiskerLeft (right c qF) (rightCompositionIso a b qD qE).hom) =
      (rightCompositionIso a (b.comp (c.comp d)) qD qG).hom ≫
        whiskerRight (rightCompositionIso b (c.comp d) qE qG).hom (right a qD) ≫
          whiskerRight (whiskerRight (rightCompositionIso c d qF qG).hom (right b qE)) (right a qD) ≫
            (Functor.associator (right d qG ⋙ right c qF) (right b qE) (right a qD)).hom ≫
              (Functor.associator (right d qG) (right c qF) (right b qE ⋙ right a qD)).hom :=
  right_pentagon a b c d qD qE qF qG

/-- Source-unit coherence retains the original replacement, rather than demanding Qq=qQ. -/
theorem actualLeftSourceUnit : (leftCompositionIso (Adjunction.id (C := C)) a qC qC).hom =
    whiskerRight (leftIdentityIso qC).hom (left a qC) ≫ (Functor.leftUnitor (left a qC)).hom :=
  left_unit_source a qC

/-- Target-unit coherence keeps the actual chosen target q map. -/
theorem actualLeftTargetUnit : (leftCompositionIso a (Adjunction.id (C := D)) qC qD).hom =
    whiskerLeft (left a qC) (leftIdentityIso qD).hom ≫ (Functor.rightUnitor (left a qC)).hom :=
  left_unit_target a qC qD

/-- The original right source-unit diagram retains both complete unit transformations. -/
theorem actualRightSourceUnit : (rightCompositionIso a (Adjunction.id (C := D)) qD qD).hom =
    (Functor.leftUnitor (right a qD)).inv ≫ whiskerRight (rightIdentityIso qD).hom (right a qD) :=
  right_unit_source a qD

/-- The right target-unit diagram keeps the original chosen source r map. -/
theorem actualRightTargetUnit : (rightCompositionIso (Adjunction.id (C := C)) a qC qD).hom =
    (Functor.rightUnitor (right a qD)).inv ≫ whiskerLeft (right a qD) (rightIdentityIso qC).hom :=
  right_unit_target a qC qD

end DerivedFunctorFullClients
