/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiber

/-!
# Tests for strict Quillen Stage-grid fibers

These tests pin the standard `Functor.Fiber` carrier, all-degree nonemptiness,
the final/initial connectedness criteria, low degrees, and independent
universes.  Negative guards ensure that importing the module does not install
connectedness/finality instances or expose contractibility, weak-equivalence,
or Q/S conclusions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenStageGridFiberTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section ArbitraryDegree

variable {a : SimplexCategory} (q : QuillenQSimplex C a)

example : Type (max u v) := QuillenStageGridFiber q

example : Nonempty (QuillenStageGridFiber q) :=
  quillenStageGridFiber_nonempty q

example :
    (quillenStageGridQProjection C a).Final ↔
      ∀ q : QuillenQSimplex C a,
        IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridQProjection_final_iff C a

example :
    (quillenStageGridQProjection C a).Initial ↔
      ∀ q : QuillenQSimplex C a,
        IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridQProjection_initial_iff C a

/-- The object equality stored by the standard fiber is exactly equality of
the retained Q-simplex after unwrapping `Discrete`. -/
example (X : QuillenStageGridFiber q) : X.1.q = q := by
  exact congrArg Discrete.as X.2

/-- Fiber morphisms retain the standard `IsHomLift` proof over the identity
of the fixed discrete simplex. -/
example {X Y : QuillenStageGridFiber q} (f : X ⟶ Y) :
    (quillenStageGridQProjection C a).IsHomLift
      (𝟙 (Discrete.mk q))
      (Functor.Fiber.fiberInclusion.map f) :=
  f.2

end ArbitraryDegree

section LowDegrees

example (q₀ : QuillenQSimplex C ⦋0⦌) :
    Nonempty (QuillenStageGridFiber q₀) :=
  quillenStageGridFiber_nonempty q₀

example (q₁ : QuillenQSimplex C ⦋1⦌) :
    Nonempty (QuillenStageGridFiber q₁) :=
  quillenStageGridFiber_nonempty q₁

example (q₂ : QuillenQSimplex C ⦋2⦌) :
    Nonempty (QuillenStageGridFiber q₂) :=
  quillenStageGridFiber_nonempty q₂

example (q₃ : QuillenQSimplex C ⦋3⦌) :
    Nonempty (QuillenStageGridFiber q₃) :=
  quillenStageGridFiber_nonempty q₃

end LowDegrees

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example (q : QuillenQSimplex C₀ ⦋1⦌) :
    Nonempty (QuillenStageGridFiber q) :=
  quillenStageGridFiber_nonempty q

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example (q : QuillenQSimplex C₁ ⦋2⦌) :
    Nonempty (QuillenStageGridFiber q) :=
  quillenStageGridFiber_nonempty q

end TypeOne

section MixedObjectSmallMorphLarge

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁]
  [ExactCategory C₀₁]

example (q : QuillenQSimplex C₀₁ ⦋1⦌) :
    Nonempty (QuillenStageGridFiber q) :=
  quillenStageGridFiber_nonempty q

end MixedObjectSmallMorphLarge

section MixedObjectLargeMorphSmall

variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀]
  [ExactCategory C₁₀]

example (q : QuillenQSimplex C₁₀ ⦋3⦌) :
    Nonempty (QuillenStageGridFiber q) :=
  quillenStageGridFiber_nonempty q

end MixedObjectLargeMorphSmall

section NegativeClaims

variable {a : SimplexCategory} (q : QuillenQSimplex C a)

/-! Nonemptiness does not install any connectedness/finality instance. -/

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsConnected (QuillenStageGridFiber q)

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Final

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Initial

/-! No stronger public conclusion is introduced under a suggestive name. -/

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridFiber_contractible

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQProjection_weakEquivalence

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQSComparison

end NegativeClaims

end MathlibExtTest.KTheory.Categorical.QuillenStageGridFiberTests

end
