/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCancellation
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceRightCancellation
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion

/-!
# Quillen API integration tests

The tests keep arbitrary model categories and the original adjunct maps.
Cancellation assumes an equivalence of the actual composite, rather than
the conclusion for the adjunction being tested. Brown preservation retains
its cofibrant-source or fibrant-target restrictions.

The original ATLAS integration tests are by Tsutomu Okano.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uC uD uE vC vD vE

open CategoryTheory HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenAPI

section Identity

variable (C : Type uC) [Category.{vC} C] [ModelCategory C]

example : (Adjunction.id (C := C)).IsQuillenAdjunction := inferInstance

example : (Adjunction.id (C := C)).IsQuillenEquivalence := inferInstance

-- Exercise the complete equivalence field on every permitted original arrow.
example {X Y : C} [IsCofibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence f ↔
      WeakEquivalence ((Adjunction.id (C := C)).homEquiv X Y f) :=
  Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := Adjunction.id (C := C)) f

example (X Y : C) (f : X ⟶ Y) :
    (Adjunction.id (C := C)).homEquiv X Y f = f := by
  simp [Adjunction.homEquiv]

example (X Y : C) (f : X ⟶ Y) :
    ((Adjunction.id (C := C)).homEquiv X Y).symm f = f := by
  simp [Adjunction.homEquiv]

example : Adjunction.IsQuillenEquivalence
    ((Adjunction.id (C := C)).comp (Adjunction.id (C := C))) :=
  inferInstance

end Identity

section Preservation

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

-- Construct the left preservation witnesses from the two right classes.
example (hF : PreservesFibrations R) (hTF : PreservesTrivialFibrations R)
    {X Y : C} (i : X ⟶ Y) (hi : cofibrations C i) :
    cofibrations D (L.map i) := by
  let : adj.IsQuillenAdjunction :=
    Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
      (adj := adj) hF hTF
  exact (inferInstance : adj.IsQuillenAdjunction).preservesCofibrations i hi

example (hF : PreservesFibrations R) (hTF : PreservesTrivialFibrations R)
    {X Y : C} (i : X ⟶ Y) (hi : trivialCofibrations C i) :
    trivialCofibrations D (L.map i) := by
  let : adj.IsQuillenAdjunction :=
    Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
      (adj := adj) hF hTF
  exact (inferInstance : adj.IsQuillenAdjunction).preservesTrivialCofibrations
    i hi

example [adj.IsQuillenAdjunction] {X Y : D} (p : X ⟶ Y)
    (hp : fibrations D p) : fibrations C (R.map p) :=
  Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) p hp

example [adj.IsQuillenAdjunction] {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (L.map f) :=
  Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) f

example [adj.IsQuillenAdjunction] {X Y : D} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (R.map f) :=
  Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f

-- The restricted right-fibration criterion supplies both unrestricted preservation fields.
open Adjunction.IsQuillenAdjunction in
example (hL : PreservesCofibrations L)
    (hR : PreservesFibrationsBetweenFibrantObjects R)
    {A B : C} (i : A ⟶ B) (hi : trivialCofibrations C i)
    {X Y : D} (p : X ⟶ Y) (hp : fibrations D p) :
    trivialCofibrations D (L.map i) ∧ fibrations C (R.map p) := by
  have hQ : adj.IsQuillenAdjunction :=
    mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects (adj := adj) hL hR
  exact ⟨hQ.preservesTrivialCofibrations i hi, preservesFibrations (adj := adj) p hp⟩

-- The reverse direction returns a preservation witness for every fibrant pair.
open Adjunction.IsQuillenAdjunction in
example (hQ : adj.IsQuillenAdjunction) {X Y : D} [IsFibrant X] [IsFibrant Y]
    (p : X ⟶ Y) (hp : fibrations D p) : fibrations C (R.map p) :=
  ((iff_preservesCofibrations_and_fibrationsBetweenFibrantObjects (adj := adj)).mp hQ).2
    p ⟨hp, inferInstance, inferInstance⟩

-- Construct the Quillen structure first, then apply Brown on the left.
open Adjunction.IsQuillenAdjunction in
example (hL : PreservesCofibrations L)
    (hR : PreservesFibrationsBetweenFibrantObjects R)
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (L.map f) := by
  have : adj.IsQuillenAdjunction :=
    (iff_preservesCofibrations_and_fibrationsBetweenFibrantObjects (adj := adj)).mpr ⟨hL, hR⟩
  exact map_weakEquivalence_of_cofibrant (adj := adj) f

end Preservation

section Cancellation

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenAdjunction]

-- Neither test assumes that the original adjunction is already an equivalence.
example [((Adjunction.id (C := C)).comp adj).IsQuillenEquivalence] :
    adj.IsQuillenEquivalence :=
  Adjunction.IsQuillenEquivalence.cancel_left (Adjunction.id (C := C)) adj

example [(adj.comp (Adjunction.id (C := D))).IsQuillenEquivalence] :
    adj.IsQuillenEquivalence :=
  Adjunction.IsQuillenEquivalence.cancel_right adj (Adjunction.id (C := D))

-- Check that cancellation returns the full criterion for this original map.
example [((Adjunction.id (C := C)).comp adj).IsQuillenEquivalence]
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f) := by
  let : adj.IsQuillenEquivalence :=
    Adjunction.IsQuillenEquivalence.cancel_left (Adjunction.id (C := C)) adj
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := adj) f

example [(adj.comp (Adjunction.id (C := D))).IsQuillenEquivalence]
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f) := by
  let : adj.IsQuillenEquivalence :=
    Adjunction.IsQuillenEquivalence.cancel_right adj (Adjunction.id (C := D))
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := adj) f

end Cancellation

section GeneralCancellation

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
  (adj : L ⊣ R) (adj' : L' ⊣ R')

-- Use the actual three-category composite, with neither factor fixed.
example [adj.IsQuillenEquivalence] [adj'.IsQuillenAdjunction]
    [(adj.comp adj').IsQuillenEquivalence] :
    adj'.IsQuillenEquivalence :=
  Adjunction.IsQuillenEquivalence.cancel_left adj adj'

example [adj.IsQuillenEquivalence] [adj'.IsQuillenAdjunction]
    [(adj.comp adj').IsQuillenEquivalence]
    {X : D} {Y : E} [IsCofibrant X] [IsFibrant Y] (f : L'.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj'.homEquiv X Y f) := by
  let : adj'.IsQuillenEquivalence :=
    Adjunction.IsQuillenEquivalence.cancel_left adj adj'
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := adj') f

example [adj.IsQuillenAdjunction] [adj'.IsQuillenEquivalence]
    [(adj.comp adj').IsQuillenEquivalence] :
    adj.IsQuillenEquivalence :=
  Adjunction.IsQuillenEquivalence.cancel_right adj adj'

example [adj.IsQuillenAdjunction] [adj'.IsQuillenEquivalence]
    [(adj.comp adj').IsQuillenEquivalence]
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f) := by
  let : adj.IsQuillenEquivalence :=
    Adjunction.IsQuillenEquivalence.cancel_right adj adj'
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := adj) f

end GeneralCancellation

end MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenAPI
