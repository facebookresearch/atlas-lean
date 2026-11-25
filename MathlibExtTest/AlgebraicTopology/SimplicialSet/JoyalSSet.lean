/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalSSet
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The designated simplicial category

The native induced category and ordinary forgetful equivalence retain
the underlying simplicial sets and maps. Model structures are separate
data on this designated carrier.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.JoyalSSet

/-- Wrapping and forgetting retain the complete simplicial map. -/
theorem mapRoundTrip {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.JoyalSSet.forget.map (_root_.JoyalSSet.ofSSet.map f) = f := rfl

/-- The native Hom equivalence retains the same full simplicial map. -/
theorem homEquivRoundTrip {X Y : _root_.JoyalSSet.{u}} (f : X.toSSet ⟶ Y.toSSet) :
    _root_.JoyalSSet.forget.map (_root_.JoyalSSet.homEquiv.symm f) = f := rfl

/-- The product comparison is an actual isomorphism of simplicial sets. -/
def productIso (X Y : _root_.JoyalSSet.{u}) :
    _root_.JoyalSSet.forget.obj (X ⨯ Y) ≅ X.toSSet ⨯ Y.toSSet :=
  PreservesLimitPair.iso _root_.JoyalSSet.forget X Y

/-- The comparison keeps the first product projection. -/
theorem productIso_fst (X Y : _root_.JoyalSSet.{u}) :
    (productIso X Y).hom ≫ prod.fst =
      _root_.JoyalSSet.forget.map (prod.fst : X ⨯ Y ⟶ X) := by
  simpa only [productIso, PreservesLimitPair.iso_hom, _root_.JoyalSSet.forget_obj] using!
    (prodComparison_fst _root_.JoyalSSet.forget X Y)

/-- The comparison keeps the second product projection. -/
theorem productIso_snd (X Y : _root_.JoyalSSet.{u}) :
    (productIso X Y).hom ≫ prod.snd =
      _root_.JoyalSSet.forget.map (prod.snd : X ⨯ Y ⟶ Y) := by
  simpa only [productIso, PreservesLimitPair.iso_hom, _root_.JoyalSSet.forget_obj] using!
    (prodComparison_snd _root_.JoyalSSet.forget X Y)

/-- Both mapped projections satisfy the actual product universal property. -/
def mappedProductIsLimit (X Y : _root_.JoyalSSet.{u}) :
    IsLimit (BinaryFan.mk
      (_root_.JoyalSSet.forget.map (prod.fst : X ⨯ Y ⟶ X))
      (_root_.JoyalSSet.forget.map (prod.snd : X ⨯ Y ⟶ Y))) :=
  isLimitOfHasBinaryProductOfPreservesLimit _root_.JoyalSSet.forget X Y

section Diagrams

variable {J : Type v} [Category.{w} J] {F : J ⥤ _root_.JoyalSSet.{u}}

/-- Forgetting takes an actual limiting cone to a limiting cone. -/
def preserveCone (c : Cone F) (hc : IsLimit c) :
    IsLimit (_root_.JoyalSSet.forget.mapCone c) :=
  isLimitOfPreserves _root_.JoyalSSet.forget hc

/-- A limiting mapped cone gives the original cone's full universal property. -/
def reflectCone (c : Cone F) (hc : IsLimit (_root_.JoyalSSet.forget.mapCone c)) :
    IsLimit c :=
  isLimitOfReflects _root_.JoyalSSet.forget hc

/-- Forgetting takes an actual colimiting cocone to a colimiting cocone. -/
def preserveCocone (c : Cocone F) (hc : IsColimit c) :
    IsColimit (_root_.JoyalSSet.forget.mapCocone c) :=
  isColimitOfPreserves _root_.JoyalSSet.forget hc

/-- A colimiting mapped cocone gives the original cocone's full universal property. -/
def reflectCocone (c : Cocone F)
    (hc : IsColimit (_root_.JoyalSSet.forget.mapCocone c)) : IsColimit c :=
  isColimitOfReflects _root_.JoyalSSet.forget hc

end Diagrams

/-- Arbitrary object predicates pull back without an isomorphism-invariance premise. -/
example (P : ObjectProperty SSet.{u}) (X : _root_.JoyalSSet.{u}) :
    _root_.JoyalSSet.transportObjectProperty P X ↔ P X.toSSet := by simp

/-- Arbitrary morphism predicates test the actual underlying simplicial map. -/
example (P : MorphismProperty SSet.{u}) {X Y : _root_.JoyalSSet.{u}} (f : X ⟶ Y) :
    _root_.JoyalSSet.transportMorphismProperty P f ↔
      P (_root_.JoyalSSet.forget.map f) := by simp

end MathlibExtTest.AlgebraicTopology.SimplicialSet.JoyalSSet
