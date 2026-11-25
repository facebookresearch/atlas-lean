/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Proper

/-!
# Original projective properness clients

The small-index controls assume only actual generation, without coefficient
local presentability. The original-index controls keep an arbitrary original
presentation. Canonical pushout and pullback controls check the actual weak
legs, and the two-rank control keeps independent source choices.
-/

set_option autoImplicit false
noncomputable section

universe w w' uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace FunctorProjectiveProperTests

section SmallIndex

variable {D : Type uD} [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The weak leg is the first canonical injection of the original pushout.
No local-presentability or combinatorial coefficient premise is used. -/
theorem canonicalPushoutComponents [IsLeftProper C] {A B X : D ⥤ C}
    (i : A ⟶ B) (f : A ⟶ X) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    cofibrations (D ⥤ C) i → weakEquivalences (D ⥤ C) f →
      ∀ a : D, weakEquivalences C ((pushout.inl i f).app a) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
  let : IsLeftProper (D ⥤ C) := FunctorProjective.modelCategory_isLeftProper d
  intro hi hf
  let : Cofibration i := (cofibration_iff _).mpr hi
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  have h := (weakEquivalence_iff _).mp
    (IsLeftProper.weakEquivalence_of_isPushout (IsPushout.of_hasPushout i f))
  rw [FunctorProjective.weakEquivalences_eq d] at h
  exact h

/-- The weak leg is the second projection of the original canonical pullback. -/
theorem canonicalPullbackComponents [IsRightProper C] {B X Y : D ⥤ C}
    (f : B ⟶ Y) (p : X ⟶ Y) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    fibrations (D ⥤ C) p → weakEquivalences (D ⥤ C) f →
      ∀ a : D, weakEquivalences C ((pullback.snd f p).app a) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
  let : IsRightProper (D ⥤ C) := FunctorProjective.modelCategory_isRightProper d
  intro hp hf
  let : Fibration p := (fibration_iff _).mpr hp
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  have h := (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback f p))
  rw [FunctorProjective.weakEquivalences_eq d] at h
  exact h

end SmallIndex

section OriginalIndex

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} D C)

/-- A given original square keeps every original component of its pushed arrow.
The original index is not assumed small in this presentation. -/
theorem originalPushoutComponents [IsLeftProper C] {A B X Y : D ⥤ C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d s
    cofibrations (D ⥤ C) i → weakEquivalences (D ⥤ C) f →
      ∀ a : D, weakEquivalences C (f'.app a) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d s
  intro hi hf
  have h := FunctorProjective.SourceConstruction.FromData.weakEquivalence_of_isPushout d s sq hi hf
  rw [(FunctorProjective.SourceConstruction.FromData.five_classes d s).1] at h
  exact h

/-- A given original pullback square retains the literal second leg at every object. -/
theorem originalPullbackComponents [IsRightProper C] {A B X Y : D ⥤ C}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d s
    fibrations (D ⥤ C) p → weakEquivalences (D ⥤ C) f →
      ∀ a : D, weakEquivalences C (f'.app a) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d s
  intro hp hf
  have h := FunctorProjective.SourceConstruction.FromData.weakEquivalence_of_isPullback d s sq hp hf
  rw [(FunctorProjective.SourceConstruction.FromData.five_classes d s).1] at h
  exact h

variable {κ' : Cardinal.{w'}} [Fact κ'.IsRegular] [OrderBot κ'.ord.ToType]
  (d' : CofibrantGenerationData C κ') (s' : Functor.EssentialIndexData.{w'} D C)

/-- A pushed original weak map remains weak under an independent source rank,
working universe and full small-index choice. -/
theorem crossChoicePushoutWeak [IsLeftProper C] {A B X Y : D ⥤ C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d s
    cofibrations (D ⥤ C) i → weakEquivalences (D ⥤ C) f →
      (letI : ModelCategory (D ⥤ C) :=
         FunctorProjective.SourceConstruction.FromData.modelCategory d' s'
       weakEquivalences (D ⥤ C) f') := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.FromData.modelCategory d s
  intro hi hf
  have h := FunctorProjective.SourceConstruction.FromData.weakEquivalence_of_isPushout d s sq hi hf
  rw [(FunctorProjective.SourceConstruction.FromData.five_classes d s).1] at h
  exact (FunctorProjective.SourceConstruction.FromData.five_classes d' s').1.symm ▸ h

end OriginalIndex

section ConventionalSources

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C]

/-- The public source factory supplies properness of its own actual model. -/
theorem publicSourcePushoutWeak [IsLeftProper C] {A B X Y : D ⥤ C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    cofibrations (D ⥤ C) i → weakEquivalences (D ⥤ C) f →
      ∀ a : D, weakEquivalences C (f'.app a) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
  let : IsLeftProper (D ⥤ C) := FunctorProjective.SourceConstruction.isLeftProper
  intro hi hf
  let : Cofibration i := (cofibration_iff _).mpr hi
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  have h := (weakEquivalence_iff _).mp (IsLeftProper.weakEquivalence_of_isPushout sq)
  rw [(FunctorProjective.SourceConstruction.five_classes (D := D) (C := C)).1] at h
  exact h

/-- Right properness is independently supplied by that same original public model. -/
theorem publicSourcePullbackWeak [IsRightProper C] {A B X Y : D ⥤ C}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
    fibrations (D ⥤ C) p → weakEquivalences (D ⥤ C) f →
      ∀ a : D, weakEquivalences C (f'.app a) := by
  let : ModelCategory (D ⥤ C) := FunctorProjective.SourceConstruction.modelCategory
  let : IsRightProper (D ⥤ C) := FunctorProjective.SourceConstruction.isRightProper
  intro hp hf
  let : Fibration p := (fibration_iff _).mpr hp
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  have h := (weakEquivalence_iff _).mp (IsRightProper.weakEquivalence_of_isPullback sq)
  rw [(FunctorProjective.SourceConstruction.five_classes (D := D) (C := C)).1] at h
  exact h

end ConventionalSources

end FunctorProjectiveProperTests
