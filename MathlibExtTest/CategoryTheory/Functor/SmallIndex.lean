/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Types.Basic
import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence

/-!
# Small index models and transport of natural transformations
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uM vM

open CategoryTheory

section IndependentUniverses

variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
variable {S : Type w} [SmallCategory S] (e : D ≌ S)

example {F G : D ⥤ M} {α β : F ⟶ G}
    (h : ∀ d : S, α.app (e.inverse.obj d) = β.app (e.inverse.obj d)) : α = β :=
  (e.congrLeft (E := M)).functor.map_injective (NatTrans.ext (funext h))

example {F G : D ⥤ M} (α : F ⟶ G) (d : S) :
    ((e.congrLeft (E := M)).functor.map α).app d = α.app (e.inverse.obj d) := rfl

example {F G : S ⥤ M} (α : F ⟶ G) (d : D) :
    ((e.congrLeft (E := M)).inverse.map α).app d = α.app (e.functor.obj d) := rfl

end IndependentUniverses

example (D : Type uD) [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D] :
    D ≌ SmallModel.{w} D := equivSmallModel.{w} D

example : Discrete PEmpty ≌ SmallModel.{0} (Discrete PEmpty) := equivSmallModel.{0} _

example : Discrete ℕ ≌ SmallModel.{0} (Discrete ℕ) := equivSmallModel.{0} _

example : Discrete Bool ≌ SmallModel.{0} (Discrete Bool) := equivSmallModel.{0} _

/- The original object carrier can live strictly above the working universe. -/
example : Discrete (ULift.{1} Bool) ≌ SmallModel.{0} (Discrete (ULift.{1} Bool)) :=
  equivSmallModel.{0} _

private abbrev LargeIndex := Discrete (ULift.{1} Bool)
private abbrev SmallIndex := SmallModel.{0} LargeIndex
private def indexEquiv : LargeIndex ≌ SmallIndex := equivSmallModel.{0} LargeIndex

private def negation : (Bool : Type) ≅ Bool :=
  Equiv.toIso ⟨Bool.not, Bool.not, by intro x; cases x <;> rfl, by intro x; cases x <;> rfl⟩

private abbrev bits : LargeIndex ⥤ Type := (Functor.const LargeIndex).obj Bool
private def flipBits : bits ⟶ bits := (Functor.const LargeIndex).map negation.hom

private abbrev isoProperty : MorphismProperty (Type) := MorphismProperty.isomorphisms (Type)

-- Transport the pointwise isomorphism to universe 0 and back through the actual small model.
example :
    (isoProperty.functorCategory LargeIndex)
      ((indexEquiv.congrLeft (E := Type)).inverse.map
        ((indexEquiv.congrLeft (E := Type)).functor.map flipBits)) ∧
    (((indexEquiv.congrLeft (E := Type)).functor.map flipBits).app
      (indexEquiv.functor.obj ⟨ULift.up true⟩)) true = false := by
  have atRepresentatives : (isoProperty.functorCategory SmallIndex)
      ((indexEquiv.congrLeft (E := Type)).functor.map flipBits) := by
    change ((isoProperty.functorCategory SmallIndex).inverseImage
      (indexEquiv.congrLeft (E := Type)).functor) flipBits
    rw [MorphismProperty.functorCategory_inverseImage_congrLeft]
    intro d
    change IsIso negation.hom
    infer_instance
  refine ⟨?_, rfl⟩
  change ((isoProperty.functorCategory LargeIndex).inverseImage
    (indexEquiv.congrLeft (E := Type)).inverse)
      ((indexEquiv.congrLeft (E := Type)).functor.map flipBits)
  rw [MorphismProperty.functorCategory_inverseImage_congrLeft_inverse]
  exact atRepresentatives
