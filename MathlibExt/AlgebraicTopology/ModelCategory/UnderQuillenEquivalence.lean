/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.Under
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Quillen equivalences on Under categories

A Quillen adjunction induces a Quillen adjunction on Under categories by
postcomposition. If the source base object is cofibrant, a Quillen
equivalence induces a Quillen equivalence. An isomorphism from the image of
the source base to a preferred target base may be incorporated explicitly.

All results are named values. This file installs no Quillen instance.
-/

set_option autoImplicit false

noncomputable section

universe vC vD uC uD

open CategoryTheory HomotopicalAlgebra CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
variable {D : Type uD} [Category.{vD} D] [ModelCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

private theorem isCofibrant_right_of_under
    {S : C} (hS : IsCofibrant S)
    {X : Under S} (hX : IsCofibrant X) :
    IsCofibrant X.right := by
  have hι : Cofibration (Under.mkIdInitial.to X) :=
    (isCofibrant_iff_of_isInitial
      (Under.mkIdInitial.to X) Under.mkIdInitial).mp hX
  have hhom : Cofibration X.hom := by
    rw [cofibrations_under_iff S] at hι
    simpa using hι
  let _ : IsCofibrant S := hS
  let _ : Cofibration X.hom := hhom
  exact isCofibrant_of_cofibration X.hom

private theorem isFibrant_right_of_under
    {T : D} {Y : Under T} (hY : IsFibrant Y) :
    IsFibrant Y.right := by
  let Z : Under T := Under.mk (terminal.from T)
  have hZ : IsTerminal Z := by
    refine IsTerminal.ofUniqueHom
      (fun A => Under.homMk (terminal.from A.right) (by
        dsimp [Z]
        exact terminalIsTerminal.hom_ext _ _)) ?_
    intro A f
    apply Under.UnderMorphism.ext
    dsimp [Z]
    exact terminalIsTerminal.hom_ext _ _
  let p : Y ⟶ Z :=
    Under.homMk (terminal.from Y.right) (by
      dsimp [Z]
      exact terminalIsTerminal.hom_ext _ _)
  have hp : Fibration p :=
    (isFibrant_iff_of_isTerminal p hZ).mp hY
  have hpRight : Fibration p.right :=
    (fibrations_under_iff T p).mp hp
  change Fibration (terminal.from Y.right)
  simpa [p] using hpRight

omit [ModelCategory C] [ModelCategory D] in
private theorem postAdjunctionLeft_homEquiv_right
    {S : C} (X : Under S) (Y : Under (L.obj S))
    (f : (Under.post L).obj X ⟶ Y) :
    (((Under.postAdjunctionLeft (X := S) adj).homEquiv X Y) f).right =
      (adj.homEquiv X.right Y.right) f.right := by
  rfl

omit [ModelCategory C] in
private theorem mapIso_homEquiv_right
    {S T : C} (e : S ≅ T) (X : Under T) (Y : Under S)
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

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

/-- Postcomposition lifts a Quillen adjunction to every Under category. -/
theorem underPost
    (h : IsQuillenAdjunction adj) (S : C) :
    IsQuillenAdjunction
      (CategoryTheory.Under.postAdjunctionLeft (X := S) adj) where
  preservesCofibrations := by
    intro X Y f hf
    have hfRight : cofibrations C f.right := by
      simpa [cofibrations_under_def,
        CategoryTheory.MorphismProperty.under_iff] using hf
    change cofibrations D (L.map f.right)
    exact h.preservesCofibrations _ hfRight
  preservesTrivialCofibrations := by
    intro X Y f hf
    have hfRight : trivialCofibrations C f.right := by
      simpa [trivialCofibrations_under_eq,
        CategoryTheory.MorphismProperty.under_iff] using hf
    change trivialCofibrations D (L.map f.right)
    exact h.preservesTrivialCofibrations _ hfRight

end CategoryTheory.Adjunction.IsQuillenAdjunction

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- A Quillen equivalence induces a Quillen equivalence on the Under
category of a cofibrant source base. -/
theorem underPost
    (h : IsQuillenEquivalence adj) (S : C)
    (hS : IsCofibrant S) :
    IsQuillenEquivalence
      (CategoryTheory.Under.postAdjunctionLeft (X := S) adj) where
  toIsQuillenAdjunction := h.toIsQuillenAdjunction.underPost S
  homEquiv_weakEquivalence_iff {X Y} hX hY f := by
    let _ : IsCofibrant X.right :=
      isCofibrant_right_of_under hS (X := X) hX
    let _ : IsFibrant Y.right :=
      isFibrant_right_of_under (Y := Y) hY
    calc
      weakEquivalences (Under (L.obj S)) f ↔
          weakEquivalences D f.right := by
        rw [weakEquivalences_under_def,
          CategoryTheory.MorphismProperty.under_iff]
      _ ↔ weakEquivalences C
          ((adj.homEquiv X.right Y.right) f.right) :=
        h.homEquiv_weakEquivalence_iff f.right
      _ ↔ weakEquivalences C
          (((Under.postAdjunctionLeft (X := S) adj).homEquiv X Y) f).right := by
        rw [postAdjunctionLeft_homEquiv_right]
      _ ↔ weakEquivalences (Under S)
          ((Under.postAdjunctionLeft (X := S) adj).homEquiv X Y f) := by
        rw [weakEquivalences_under_def,
          CategoryTheory.MorphismProperty.under_iff]

end CategoryTheory.Adjunction.IsQuillenEquivalence

namespace CategoryTheory.Under

/-- Changing the base of an Under category along an isomorphism is a
Quillen equivalence. -/
theorem mapIso_isQuillenEquivalence
    {C : Type uC} [Category.{vC} C] [ModelCategory C]
    {S T : C} (e : S ≅ T) :
    Adjunction.IsQuillenEquivalence (Under.mapIso e).toAdjunction where
  toIsQuillenAdjunction := {
    preservesCofibrations := by
      intro X Y f hf
      change cofibrations C f.right
      simpa [cofibrations_under_def,
        CategoryTheory.MorphismProperty.under_iff] using hf
    preservesTrivialCofibrations := by
      intro X Y f hf
      change trivialCofibrations C f.right
      simpa [trivialCofibrations_under_eq,
        CategoryTheory.MorphismProperty.under_iff] using hf }
  homEquiv_weakEquivalence_iff {X Y} _hX _hY f := by
    calc
      weakEquivalences (Under S) f ↔ weakEquivalences C f.right := by
        rw [weakEquivalences_under_def,
          CategoryTheory.MorphismProperty.under_iff]
      _ ↔ weakEquivalences C
          (((Under.mapIso e).toAdjunction.homEquiv X Y) f).right := by
        rw [mapIso_homEquiv_right]
        rfl
      _ ↔ weakEquivalences (Under T)
          ((Under.mapIso e).toAdjunction.homEquiv X Y f) := by
        rw [weakEquivalences_under_def,
          CategoryTheory.MorphismProperty.under_iff]

omit [ModelCategory C] [ModelCategory D] in
/-- The induced Under adjunction with its target base changed along an
isomorphism from the image of the source base. -/
noncomputable def postAdjunctionLeftOfIso
    (adj : L ⊣ R) (S : C) {T : D} (e : L.obj S ≅ T) :
    (Under.post L ⋙ (Under.mapIso e.symm).functor) ⊣
      ((Under.mapIso e.symm).inverse ⋙
        Under.post R ⋙ Under.map (adj.unit.app S)) :=
  (Under.postAdjunctionLeft (X := S) adj).comp
    (Under.mapIso e.symm).toAdjunction

end CategoryTheory.Under

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- A Quillen equivalence induces a Quillen equivalence on compatible
Under categories when the source base is cofibrant. -/
theorem underPostOfIso
    (h : IsQuillenEquivalence adj) (S : C)
    (hS : IsCofibrant S) {T : D} (e : L.obj S ≅ T) :
    IsQuillenEquivalence
      (CategoryTheory.Under.postAdjunctionLeftOfIso adj S e) := by
  let _ : IsQuillenEquivalence
      (Under.postAdjunctionLeft (X := S) adj) :=
    h.underPost S hS
  let _ : IsQuillenEquivalence
      (Under.mapIso e.symm).toAdjunction :=
    Under.mapIso_isQuillenEquivalence e.symm
  change IsQuillenEquivalence
    ((Under.postAdjunctionLeft (X := S) adj).comp
      (Under.mapIso e.symm).toAdjunction)
  infer_instance

end CategoryTheory.Adjunction.IsQuillenEquivalence
