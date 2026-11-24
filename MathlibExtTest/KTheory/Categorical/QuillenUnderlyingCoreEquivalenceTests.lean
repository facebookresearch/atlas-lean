/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenUnderlyingCoreEquivalence

/-!
# Tests for the core of the Quillen Q-construction

These tests exercise exact Q-isomorphism lifting, injectivity of the
underlying-isomorphism lift, the exact fully faithful preimage, the bundled
core equivalence, independent object/morphism universes, and the lower-layer
import boundary.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenUnderlyingCoreEquivalenceTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section ExactLiftsAndInjectivity

variable {X Y : C}

example (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) :
    Nonempty { f : X ≅ Y // QuillenQ.underlyingIso f = e } :=
  quillenQ_iso_lifts_to_underlying_iso_eq e

example (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) : Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso e

example (e f : X ≅ Y)
    (h : (QuillenQ.underlyingIso e).hom =
      (QuillenQ.underlyingIso f).hom) :
    e = f :=
  QuillenQ.underlyingIso_hom_injective h

example (e f : X ≅ Y)
    (h : QuillenQ.underlyingIso e = QuillenQ.underlyingIso f) :
    e = f :=
  QuillenQ.underlyingIso_injective h

example (X : C) :
    QuillenQ.underlyingIso (Iso.refl X) =
      Iso.refl (⟨X⟩ : QuillenQ C) :=
  QuillenQ.underlyingIso_refl X

end ExactLiftsAndInjectivity

section CoreApi

example : Core C ⥤ Core (QuillenQ C) :=
  QuillenQ.underlyingCoreFunctor C

example (X : Core C) :
    (QuillenQ.underlyingCoreFunctor C).obj X =
      ⟨(⟨X.of⟩ : QuillenQ C)⟩ := by
  simp

example {X Y : Core C} (f : X ⟶ Y) :
    ((QuillenQ.underlyingCoreFunctor C).map f).iso =
      QuillenQ.underlyingIso f.iso := by
  simp

example : (QuillenQ.underlyingCoreFunctor C).FullyFaithful :=
  QuillenQ.underlyingCoreFunctor_fullyFaithful C

/-- Fullness recovers an exact-category isomorphism inducing exactly the
supplied Q-isomorphism, not merely an isomorphic representative. -/
example {X Y : Core C}
    (f : (QuillenQ.underlyingCoreFunctor C).obj X ⟶
      (QuillenQ.underlyingCoreFunctor C).obj Y) :
    QuillenQ.underlyingIso
        (((QuillenQ.underlyingCoreFunctor_fullyFaithful C).preimage f).iso) =
      f.iso :=
  QuillenQ.underlyingCoreFunctor_fullyFaithful_preimage_iso C f

example : Core C ≌ Core (QuillenQ C) :=
  QuillenQ.underlyingCoreEquivalence C

example :
    (QuillenQ.underlyingCoreEquivalence C).functor =
      QuillenQ.underlyingCoreFunctor C := by
  simp

end CoreApi

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example : (QuillenQ.underlyingCoreFunctor C₀).FullyFaithful :=
  QuillenQ.underlyingCoreFunctor_fullyFaithful C₀

example : Core C₀ ≌ Core (QuillenQ C₀) :=
  QuillenQ.underlyingCoreEquivalence C₀

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example : (QuillenQ.underlyingCoreFunctor C₁).FullyFaithful :=
  QuillenQ.underlyingCoreFunctor_fullyFaithful C₁

example : Core C₁ ≌ Core (QuillenQ C₁) :=
  QuillenQ.underlyingCoreEquivalence C₁

end TypeOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example : Core C₀₁ ≌ Core (QuillenQ C₀₁) :=
  QuillenQ.underlyingCoreEquivalence C₀₁

example : Core C₁₀ ≌ Core (QuillenQ C₁₀) :=
  QuillenQ.underlyingCoreEquivalence C₁₀

end MixedUniverses

section NoGlobalInstances

variable (C)

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (QuillenQ.underlyingCoreFunctor C).Full

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (QuillenQ.underlyingCoreFunctor C).Faithful

end NoGlobalInstances

section LowerImportBoundary

/-! Importing the lower core module does not expose Stage-grid APIs. -/

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.QuillenStageGridFiber

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridFiber_degreeZero_isConnected

end LowerImportBoundary

#print axioms AlgebraicKTheory.quillenQ_iso_lifts_to_underlying_iso_eq
#print axioms AlgebraicKTheory.QuillenQ.underlyingIso_hom_injective
#print axioms AlgebraicKTheory.QuillenQ.underlyingIso_injective
#print axioms AlgebraicKTheory.QuillenQ.underlyingCoreFunctor_fullyFaithful
#print axioms AlgebraicKTheory.QuillenQ.underlyingCoreFunctor_fullyFaithful_preimage_iso
#print axioms AlgebraicKTheory.QuillenQ.underlyingCoreEquivalence

end MathlibExtTest.KTheory.Categorical.QuillenUnderlyingCoreEquivalenceTests

end
