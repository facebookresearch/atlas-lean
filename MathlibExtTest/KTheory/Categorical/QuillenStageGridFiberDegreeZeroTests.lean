/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiberDegreeZero

/-!
# Tests for degree-zero Quillen Stage-grid fibers

These tests pin the existential lifting of Q-isomorphisms, degree-zero fiber
connectedness, identity and underlying-isomorphism inputs, and independent
object/morphism universes.  Negative guards ensure that the module installs no
connectedness instance and exposes no positive-degree, contractibility,
finality, weak-equivalence, or Q/S conclusion.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenStageGridFiberDegreeZeroTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section PublicUse

variable {X Y : C}

example (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) :
    Nonempty { f : X ≅ Y // QuillenQ.underlyingIso f = e } :=
  quillenQ_iso_lifts_to_underlying_iso_eq e

example (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) : Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso e

/-- The theorem accepts the identity Q-isomorphism without any balancedness
or abelian-category instance. -/
example (X : C) : Nonempty (X ≅ X) :=
  quillenQ_iso_lifts_to_underlying_iso
    (Iso.refl (⟨X⟩ : QuillenQ C))

/-- An isomorphism already coming from the exact category is a public input. -/
example (e : X ≅ Y) : Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso (QuillenQ.underlyingIso e)

example (e : X ≅ Y) :
    Nonempty { f : X ≅ Y //
      QuillenQ.underlyingIso f = QuillenQ.underlyingIso e } :=
  quillenQ_iso_lifts_to_underlying_iso_eq (QuillenQ.underlyingIso e)

example (e : (⟨X⟩ : QuillenQ C) ≅ ⟨Y⟩) :
    Nonempty { f : Y ≅ X // QuillenQ.underlyingIso f = e.symm } :=
  quillenQ_iso_lifts_to_underlying_iso_eq e.symm

/-- The degree-zero consumer publicly re-exports the canonical lower core
equivalence after the C1F-A refactor. -/
example : Core C ≌ Core (QuillenQ C) :=
  QuillenQ.underlyingCoreEquivalence C

example (q : QuillenQSimplex C ⦋0⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_degreeZero_isConnected q

end PublicUse

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example {X Y : C₀} (e : (⟨X⟩ : QuillenQ C₀) ≅ ⟨Y⟩) :
    Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso e

example (q : QuillenQSimplex C₀ ⦋0⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_degreeZero_isConnected q

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example {X Y : C₁} (e : (⟨X⟩ : QuillenQ C₁) ≅ ⟨Y⟩) :
    Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso e

example (q : QuillenQSimplex C₁ ⦋0⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_degreeZero_isConnected q

end TypeOne

section MixedObjectSmallMorphLarge

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁]
  [ExactCategory C₀₁]

example {X Y : C₀₁} (e : (⟨X⟩ : QuillenQ C₀₁) ≅ ⟨Y⟩) :
    Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso e

example (q : QuillenQSimplex C₀₁ ⦋0⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_degreeZero_isConnected q

end MixedObjectSmallMorphLarge

section MixedObjectLargeMorphSmall

variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀]
  [ExactCategory C₁₀]

example {X Y : C₁₀} (e : (⟨X⟩ : QuillenQ C₁₀) ≅ ⟨Y⟩) :
    Nonempty (X ≅ Y) :=
  quillenQ_iso_lifts_to_underlying_iso e

example (q : QuillenQSimplex C₁₀ ⦋0⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_degreeZero_isConnected q

end MixedObjectLargeMorphSmall

section NegativeClaims

variable (q : QuillenQSimplex C ⦋0⦌)

/-! The theorem is not installed as a global connectedness instance. -/

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsConnected (QuillenStageGridFiber q)

/-! No stronger public conclusion is introduced under a suggestive name. -/

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridFiber_allDegree_isConnected

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridFiber_contractible

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQProjection_degreeZero_final

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQProjection_weakEquivalence

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQSComparison

end NegativeClaims

#print axioms AlgebraicKTheory.quillenQ_iso_lifts_to_underlying_iso
#print axioms AlgebraicKTheory.quillenQ_iso_lifts_to_underlying_iso_eq
#print axioms AlgebraicKTheory.quillenStageGridFiber_degreeZero_isConnected

end MathlibExtTest.KTheory.Categorical.QuillenStageGridFiberDegreeZeroTests

end
