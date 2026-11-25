/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.UnderQuillenEquivalence

/-!
# Tests for Quillen equivalences on Under categories

These tests pin the induced adjunctions, right-component formulas, Hovey
criteria, universe behavior, explicit cofibrant-base premise, privacy, and
absence of automatically installed Quillen instances.
-/

set_option autoImplicit false

noncomputable section

universe vC vD uC uD

open CategoryTheory HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
variable {D : Type uD} [Category.{vD} D] [ModelCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

#check Adjunction.IsQuillenAdjunction.underPost
#check Adjunction.IsQuillenEquivalence.underPost
#check Under.mapIso_isQuillenEquivalence
#check Under.postAdjunctionLeftOfIso
#check Adjunction.IsQuillenEquivalence.underPostOfIso

section InducedAdjunction

variable (S : C)

example (X : Under S) :
    ((Under.postAdjunctionLeft adj).unit.app X).right =
      adj.unit.app X.right := rfl

example (Y : Under (L.obj S)) :
    ((Under.post R ⋙ Under.map (adj.unit.app S)).obj Y).hom =
      adj.unit.app S ≫ R.map Y.hom := rfl

example (X : Under S) (Y : Under (L.obj S))
    (f : (Under.post L).obj X ⟶ Y) :
    (((Under.postAdjunctionLeft adj).homEquiv X Y) f).right =
      (adj.homEquiv X.right Y.right) f.right := rfl

example (h : Adjunction.IsQuillenAdjunction adj)
    {X Y : Under S} (f : X ⟶ Y)
    (hf : cofibrations (Under S) f) :
    cofibrations (Under (L.obj S)) ((Under.post L).map f) :=
  (h.underPost S).preservesCofibrations _ hf

example (h : Adjunction.IsQuillenAdjunction adj)
    {X Y : Under S} (f : X ⟶ Y)
    (hf : trivialCofibrations (Under S) f) :
    trivialCofibrations (Under (L.obj S)) ((Under.post L).map f) :=
  (h.underPost S).preservesTrivialCofibrations _ hf

end InducedAdjunction

section HoveyCriterion

variable (h : Adjunction.IsQuillenEquivalence adj)
variable (S : C) (hS : IsCofibrant S)
variable {X : Under S} {Y : Under (L.obj S)}
variable (f : (Under.post L).obj X ⟶ Y)

example [IsCofibrant X] [IsFibrant Y]
    (hf : weakEquivalences (Under (L.obj S)) f) :
    weakEquivalences (Under S)
      ((Under.postAdjunctionLeft adj).homEquiv X Y f) := by
  let _ : Adjunction.IsQuillenEquivalence
      (Under.postAdjunctionLeft adj) := h.underPost S hS
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff f |>.mp hf

example [IsCofibrant X] [IsFibrant Y]
    (hf : weakEquivalences (Under S)
    ((Under.postAdjunctionLeft adj).homEquiv X Y f)) :
    weakEquivalences (Under (L.obj S)) f := by
  let _ : Adjunction.IsQuillenEquivalence
      (Under.postAdjunctionLeft adj) := h.underPost S hS
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff f |>.mpr hf

end HoveyCriterion

section BaseIso

variable {S T : C} (e : S ≅ T)

example {X Y : Under T} (f : X ⟶ Y) :
    ((Under.mapIso e).functor.map f).right = f.right := rfl

example {X Y : Under S} (f : X ⟶ Y) :
    ((Under.mapIso e).inverse.map f).right = f.right := rfl

omit [ModelCategory C] in
private theorem mapIso_homEquiv_right_owner
    (X : Under T) (Y : Under S)
    (f : (Under.mapIso e).functor.obj X ⟶ Y) :
    (((Under.mapIso e).toAdjunction.homEquiv X Y) f).right = f.right := by
  have hunit : ((Under.mapIso e).unit.app X).right = 𝟙 X.right := by
    dsimp [Under.mapIso, Comma.mapLeftIso, Equivalence.unit]
    simp
  change (((Under.mapIso e).unit.app X) ≫
    (Under.map e.inv).map f).right = f.right
  change ((Under.mapIso e).unit.app X).right ≫
    ((Under.map e.inv).map f).right = f.right
  rw [hunit]
  rw [Under.map_map_right]
  exact Category.id_comp _

variable {X : Under T} {Y : Under S}
variable (f : (Under.mapIso e).functor.obj X ⟶ Y)

example [IsCofibrant X] [IsFibrant Y]
    (hf : weakEquivalences (Under S) f) :
    weakEquivalences (Under T)
      ((Under.mapIso e).toAdjunction.homEquiv X Y f) := by
  let _ : Adjunction.IsQuillenEquivalence
      (Under.mapIso e).toAdjunction := Under.mapIso_isQuillenEquivalence e
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff f |>.mp hf

example [IsCofibrant X] [IsFibrant Y]
    (hf : weakEquivalences (Under T)
    ((Under.mapIso e).toAdjunction.homEquiv X Y f)) :
    weakEquivalences (Under S) f := by
  let _ : Adjunction.IsQuillenEquivalence
      (Under.mapIso e).toAdjunction := Under.mapIso_isQuillenEquivalence e
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff f |>.mpr hf

example [IsCofibrant X] [IsFibrant Y] :
    (((Under.mapIso e).toAdjunction.homEquiv X Y) f).right = f.right :=
  mapIso_homEquiv_right_owner e X Y f

end BaseIso

section CompatibleBase

variable (h : Adjunction.IsQuillenEquivalence adj)
variable (S : C) (hS : IsCofibrant S)
variable {T : D} (e : L.obj S ≅ T)

#check Under.postAdjunctionLeftOfIso adj S e

example : Adjunction.IsQuillenEquivalence
    (Under.postAdjunctionLeftOfIso adj S e) :=
  h.underPostOfIso S hS e

example (X : Under S) :
    ((Under.post L ⋙ (Under.mapIso e.symm).functor).obj X).hom =
      e.inv ≫ L.map X.hom := rfl

end CompatibleBase

section UniverseZero

variable {C₀ : Type} [Category C₀] [ModelCategory C₀]

example (S : C₀) : Adjunction.IsQuillenAdjunction
    (Under.postAdjunctionLeft (X := S) (Adjunction.id (C := C₀))) :=
  (inferInstance : Adjunction.IsQuillenEquivalence
    (Adjunction.id (C := C₀))).toIsQuillenAdjunction.underPost S

example (S : C₀) (hS : IsCofibrant S) :
    Adjunction.IsQuillenEquivalence
      (Under.postAdjunctionLeft (X := S) (Adjunction.id (C := C₀))) :=
  (inferInstance : Adjunction.IsQuillenEquivalence
    (Adjunction.id (C := C₀))).underPost S hS

end UniverseZero

section UniverseOne

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]

example (S : C₁) (hS : IsCofibrant S) :
    Adjunction.IsQuillenEquivalence
      (Under.postAdjunctionLeft (X := S) (Adjunction.id (C := C₁))) :=
  (inferInstance : Adjunction.IsQuillenEquivalence
    (Adjunction.id (C := C₁))).underPost S hS

end UniverseOne

section Negative

example (S : C) :
    IsCofibrant (Under.mk (𝟙 S)) ∧
      (Under.mk (𝟙 S)).right = S := by
  constructor
  · exact (isCofibrant_iff_of_isInitial
      (𝟙 (Under.mk (𝟙 S))) Under.mkIdInitial).2 inferInstance
  · rfl

example (_h : Adjunction.IsQuillenEquivalence adj) (_S : C) : True := by
  fail_if_success
    let _ : Adjunction.IsQuillenEquivalence
        (Under.postAdjunctionLeft adj) := _h.underPost _S
  trivial

example (_h : Adjunction.IsQuillenEquivalence adj) (S : C)
    (_hTarget : IsCofibrant (L.obj S)) : True := by
  fail_if_success
    let _ : Adjunction.IsQuillenEquivalence
        (Under.postAdjunctionLeft adj) := _h.underPost S _hTarget
  trivial

example (h : Adjunction.IsQuillenEquivalence adj) (S : C)
    (_hS : IsCofibrant S) : True := by
  let _ : Adjunction.IsQuillenEquivalence adj := h
  fail_if_success
    let _ : Adjunction.IsQuillenEquivalence
        (Under.postAdjunctionLeft adj) := inferInstance
  trivial

example {S T : C} (_e : S ≅ T) : True := by
  fail_if_success
    let _ : Adjunction.IsQuillenEquivalence
        (Under.mapIso _e).toAdjunction := inferInstance
  trivial

example (S : C) {T : D} (_e : L.obj S ≅ T) : True := by
  fail_if_success
    let _ :
        (Under.post L ⋙ (Under.mapIso _e).functor) ⊣
          ((Under.mapIso _e).inverse ⋙ Under.post R ⋙
            Under.map (adj.unit.app S)) :=
      Under.postAdjunctionLeftOfIso adj S _e
  trivial

/-- error: Unknown identifier `isCofibrant_right_of_under` -/
#guard_msgs (error, substring := true) in
#check isCofibrant_right_of_under

/-- error: Unknown identifier `isFibrant_right_of_under` -/
#guard_msgs (error, substring := true) in
#check isFibrant_right_of_under

/-- error: Unknown identifier `postAdjunctionLeft_homEquiv_right` -/
#guard_msgs (error, substring := true) in
#check postAdjunctionLeft_homEquiv_right

/-- error: Unknown identifier `mapIso_homEquiv_right` -/
#guard_msgs (error, substring := true) in
#check mapIso_homEquiv_right

end Negative

#print axioms Adjunction.IsQuillenAdjunction.underPost
#print axioms Adjunction.IsQuillenEquivalence.underPost
#print axioms Under.mapIso_isQuillenEquivalence
#print axioms Under.postAdjunctionLeftOfIso
#print axioms Adjunction.IsQuillenEquivalence.underPostOfIso
