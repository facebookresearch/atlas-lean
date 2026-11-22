/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalCartesianModel
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductBrown

/-!
# Original Cartesian product weak preservation

Reuse the named Cartesian Joyal model, its proved pushout-products,
and Brown preservation for the original tensor. All original
simplicial sets are cofibrant in that model. The native Cartesian
product comparison transports the result to the identical ordinary
simplicial product map, retaining its two whole projections.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra

namespace SSet.WalkingAdjunction

attribute [local instance] JoyalSSet.modelCategory

private theorem ofSSet_cofibrant (X : SSet.{u}) : IsCofibrant (JoyalSSet.ofSSet.obj X) := by
  apply (isCofibrant_iff_of_isInitial (JoyalSSet.ofSSet.map (initial.to X))
    (initialIsInitial.isInitialObj JoyalSSet.ofSSet (⊥_ SSet.{u}))).mpr
  rw [cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations _
  rw [JoyalSSet.modelCategory_cofibrations]
  exact inferInstance

/-- The original product of a categorical weak map with an arbitrary simplicial set is categorical weak in the same value universe. -/
theorem categoricalEquivalences_whiskerRight {X Y : SSet.{u}} (f : X ⟶ Y)
    (K : SSet.{u}) (hf : categoricalEquivalences f) : categoricalEquivalences (f ▷ K) := by
  let _ : IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} :=
    JoyalSSet.isClosedSymmetricMonoidalModelCategory
  let _ : IsCofibrant (JoyalSSet.ofSSet.obj X) := ofSSet_cofibrant X
  let _ : IsCofibrant (JoyalSSet.ofSSet.obj Y) := ofSSet_cofibrant Y
  let _ : IsCofibrant (JoyalSSet.ofSSet.obj K) := ofSSet_cofibrant K
  let _ : WeakEquivalence (JoyalSSet.ofSSet.map f) := (weakEquivalence_iff _).mpr (by
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences _
    rw [JoyalSSet.modelCategory_weakEquivalences]
    exact hf)
  have hw : WeakEquivalence (JoyalSSet.ofSSet.map f ▷ JoyalSSet.ofSSet.obj K) :=
    (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := JoyalSSet.{u})).whiskerRight_weakEquivalence_of_cofibrant
      (JoyalSSet.ofSSet.map f) (JoyalSSet.ofSSet.obj K)
  have hraw : categoricalEquivalences
      (JoyalSSet.forget.map (JoyalSSet.ofSSet.map f ▷ JoyalSSet.ofSSet.obj K)) := by
    have h := (weakEquivalence_iff _).mp hw
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
    rw [JoyalSSet.modelCategory_weakEquivalences] at h
    exact h
  let eX := CartesianMonoidalCategory.prodComparisonIso JoyalSSet.forget
    (JoyalSSet.ofSSet.obj X) (JoyalSSet.ofSSet.obj K)
  let eY := CartesianMonoidalCategory.prodComparisonIso JoyalSSet.forget
    (JoyalSSet.ofSSet.obj Y) (JoyalSSet.ofSSet.obj K)
  have commutation : eX.hom ≫ (f ▷ K) =
      JoyalSSet.forget.map (JoyalSSet.ofSSet.map f ▷ JoyalSSet.ofSSet.obj K) ≫ eY.hom :=
    (CartesianMonoidalCategory.prodComparison_natural_whiskerRight JoyalSSet.forget
      (B := JoyalSSet.ofSSet.obj K) (JoyalSSet.ofSSet.map f)).symm
  exact (categoricalEquivalences.arrow_mk_iso_iff (Arrow.isoMk eX eY commutation)).mp hraw

end SSet.WalkingAdjunction
