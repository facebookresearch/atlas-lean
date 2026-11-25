/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MorphismProperty

namespace MathlibExtTest.QuillenBrown

section PublicSurface

open CategoryTheory.Adjunction.IsQuillenAdjunction

#check @map_weakEquivalence_of_cofibrant.{v₁, v₂, u₁, u₂}
#check @map_weakEquivalence_of_cofibrant.{1, 0, 1, 0}
#check @map_weakEquivalence_of_cofibrant.{1, 1, 1, 1}
#check @map_weakEquivalence_of_cofibrant.{0, 0, 0, 0}
#check @map_weakEquivalence_of_fibrant.{v₁, v₂, u₁, u₂}
#check @map_weakEquivalence_of_fibrant.{1, 0, 1, 0}
#check @map_weakEquivalence_of_fibrant.{1, 1, 1, 1}
#check @map_weakEquivalence_of_fibrant.{0, 0, 0, 0}

end PublicSurface

section GenericClients

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

example {X Y : C} (f : X ⟶ Y) [WeakEquivalence f]
    [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (L.map f) :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := adj) f

example {X Y : D} (f : X ⟶ Y) [WeakEquivalence f]
    [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (R.map f) :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
    (adj := adj) f

example (X : C) [IsCofibrant X] :
    WeakEquivalence (L.map (𝟙 X)) :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := adj) (𝟙 X)

example (X : D) [IsFibrant X] :
    WeakEquivalence (R.map (𝟙 X)) :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
    (adj := adj) (𝟙 X)

end GenericClients

section OppositeOrientation

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

example {X Y : D} (f : X ⟶ Y) [WeakEquivalence f]
    [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (R.op.map f.op) := by
  let _ : IsCofibrant (Opposite.op Y) := by
    rw [isCofibrant_iff_of_isInitial
      ((terminal.from Y).op) terminalIsTerminal.op]
    infer_instance
  let _ : IsCofibrant (Opposite.op X) := by
    rw [isCofibrant_iff_of_isInitial
      ((terminal.from X).op) terminalIsTerminal.op]
    infer_instance
  exact
    CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj.op) f.op

example {X Y : D} (f : X ⟶ Y) [WeakEquivalence f]
    [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (R.map f) := by
  let _ : IsCofibrant (Opposite.op Y) := by
    rw [isCofibrant_iff_of_isInitial
      ((terminal.from Y).op) terminalIsTerminal.op]
    infer_instance
  let _ : IsCofibrant (Opposite.op X) := by
    rw [isCofibrant_iff_of_isInitial
      ((terminal.from X).op) terminalIsTerminal.op]
    infer_instance
  have hop : WeakEquivalence (R.op.map f.op) :=
    CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj.op) f.op
  let _ : WeakEquivalence (R.op.map f.op) := hop
  have hunop : WeakEquivalence (R.op.map f.op).unop := inferInstance
  simpa [Functor.op_map] using hunop

end OppositeOrientation

section DeletionFailures

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

example {X Y : C} (f : X ⟶ Y) [WeakEquivalence f]
    [IsCofibrant Y] [CategoryTheory.Adjunction.IsQuillenAdjunction adj] :
    True := by
  fail_if_success
    let _ : WeakEquivalence (L.map f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj) f
  trivial

example {X Y : C} (f : X ⟶ Y) [WeakEquivalence f]
    [IsCofibrant X] [CategoryTheory.Adjunction.IsQuillenAdjunction adj] :
    True := by
  fail_if_success
    let _ : WeakEquivalence (L.map f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj) f
  trivial

example {X Y : D} (f : X ⟶ Y) [WeakEquivalence f]
    [IsFibrant Y] [CategoryTheory.Adjunction.IsQuillenAdjunction adj] :
    True := by
  fail_if_success
    let _ : WeakEquivalence (R.map f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := adj) f
  trivial

example {X Y : D} (f : X ⟶ Y) [WeakEquivalence f]
    [IsFibrant X] [CategoryTheory.Adjunction.IsQuillenAdjunction adj] :
    True := by
  fail_if_success
    let _ : WeakEquivalence (R.map f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := adj) f
  trivial

example {X Y : C} (_f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y]
    [CategoryTheory.Adjunction.IsQuillenAdjunction adj] : True := by
  fail_if_success
    let _ : WeakEquivalence (L.map _f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj) _f
  trivial

example {X Y : D} (_f : X ⟶ Y) [IsFibrant X] [IsFibrant Y]
    [CategoryTheory.Adjunction.IsQuillenAdjunction adj] : True := by
  fail_if_success
    let _ : WeakEquivalence (R.map _f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := adj) _f
  trivial

example {X Y : C} (f : X ⟶ Y) [WeakEquivalence f]
    [IsCofibrant X] [IsCofibrant Y] : True := by
  fail_if_success
    let _ : WeakEquivalence (L.map f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj) f
  trivial

example {X Y : D} (f : X ⟶ Y) [WeakEquivalence f]
    [IsFibrant X] [IsFibrant Y] : True := by
  fail_if_success
    let _ : WeakEquivalence (R.map f) :=
      CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := adj) f
  trivial

end DeletionFailures

section Nonclaims

#guard_msgs (error, substring := true) in
#check CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence

#guard_msgs (error, substring := true) in
#check CategoryTheory.Adjunction.IsQuillenAdjunction.preservesWeakEquivalences

#guard_msgs (error, substring := true) in
#check CategoryTheory.Adjunction.IsQuillenAdjunction.derivedFunctor

#guard_msgs (error, substring := true) in
#check CategoryTheory.Adjunction.IsQuillenAdjunction.invarianceData

#guard_msgs (error, substring := true) in
#check CategoryTheory.Adjunction.IsQuillenAdjunction.quillenEquivalence

end Nonclaims

#print axioms CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
#print axioms CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant

end MathlibExtTest.QuillenBrown
