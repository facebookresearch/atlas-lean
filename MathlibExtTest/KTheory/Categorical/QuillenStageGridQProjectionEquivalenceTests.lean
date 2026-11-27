/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridQProjectionEquivalence

/-!
# Tests for the retained-Q projection equivalence

These tests pin final-edgewise-index normalization, extracted-Q faithfulness
in low degrees, thinness of the lift and strict-fiber categories, exact
fullness on arbitrary discrete target morphisms, the bundled equivalence and
its forward functor, independent universes, and the absence of global
categorical-property instances or later homotopical claims.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenStageGridQProjectionEquivalenceTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section LowDegrees

example : (edgewiseStageQuillenSimplexFunctor C ⦋0⦌).Faithful :=
  edgewiseStageQuillenSimplexFunctor_faithful C ⦋0⦌

example : (edgewiseStageQuillenSimplexFunctor C ⦋1⦌).Faithful :=
  edgewiseStageQuillenSimplexFunctor_faithful C ⦋1⦌

example : (edgewiseStageQuillenSimplexFunctor C ⦋2⦌).Faithful :=
  edgewiseStageQuillenSimplexFunctor_faithful C ⦋2⦌

example : (quillenStageGridQProjection C ⦋0⦌).Faithful :=
  quillenStageGridQProjection_faithful C ⦋0⦌

example : (quillenStageGridQProjection C ⦋1⦌).Faithful :=
  quillenStageGridQProjection_faithful C ⦋1⦌

example : (quillenStageGridQProjection C ⦋2⦌).Faithful :=
  quillenStageGridQProjection_faithful C ⦋2⦌

example :
    interval
        (edgewiseLeftIndex ⦋0⦌ (Fin.last ⦋0⦌.len))
        (edgewiseRightIndex ⦋0⦌ (Fin.last ⦋0⦌.len))
        (edgewiseStageVertex_le ⦋0⦌ (Fin.last ⦋0⦌.len)) =
      interval 0 (Fin.last (edgewiseQ.obj ⦋0⦌).len) (Fin.zero_le _) :=
  edgewiseStageVertexIndex_last ⦋0⦌

example :
    interval
        (edgewiseLeftIndex ⦋1⦌ (Fin.last ⦋1⦌.len))
        (edgewiseRightIndex ⦋1⦌ (Fin.last ⦋1⦌.len))
        (edgewiseStageVertex_le ⦋1⦌ (Fin.last ⦋1⦌.len)) =
      interval 0 (Fin.last (edgewiseQ.obj ⦋1⦌).len) (Fin.zero_le _) :=
  edgewiseStageVertexIndex_last ⦋1⦌

example :
    interval
        (edgewiseLeftIndex ⦋2⦌ (Fin.last ⦋2⦌.len))
        (edgewiseRightIndex ⦋2⦌ (Fin.last ⦋2⦌.len))
        (edgewiseStageVertex_le ⦋2⦌ (Fin.last ⦋2⦌.len)) =
      interval 0 (Fin.last (edgewiseQ.obj ⦋2⦌).len) (Fin.zero_le _) :=
  edgewiseStageVertexIndex_last ⦋2⦌

end LowDegrees

section ProjectionApi

variable {a : SimplexCategory}

example (X Y : QuillenStageGridLift C a) : Subsingleton (X ⟶ Y) :=
  quillenStageGridLift_hom_subsingleton X Y

example (X Y : QuillenStageGridLift C a) (f g : X ⟶ Y) : f = g :=
  (quillenStageGridLift_hom_subsingleton X Y).allEq f g

example : (quillenStageGridQProjection C a).Full :=
  quillenStageGridQProjection_full C a

example : (quillenStageGridQProjection C a).Faithful :=
  quillenStageGridQProjection_faithful C a

example : (quillenStageGridQProjection C a).IsEquivalence :=
  quillenStageGridQProjection_isEquivalence C a

/-- Fullness supplies a lift whose projection is exactly an arbitrary target
morphism. -/
example {X Y : QuillenStageGridLift C a}
    (h : (quillenStageGridQProjection C a).obj X ⟶
      (quillenStageGridQProjection C a).obj Y) :
    ∃ f : X ⟶ Y, (quillenStageGridQProjection C a).map f = h :=
  (quillenStageGridQProjection_full C a).map_surjective h

section SelectedFullPreimage

local instance projectionFull :
    (quillenStageGridQProjection C a).Full :=
  quillenStageGridQProjection_full C a

example {X Y : QuillenStageGridLift C a}
    (h : (quillenStageGridQProjection C a).obj X ⟶
      (quillenStageGridQProjection C a).obj Y) :
    (quillenStageGridQProjection C a).map
        ((quillenStageGridQProjection C a).preimage h) = h :=
  (quillenStageGridQProjection C a).map_preimage h

end SelectedFullPreimage

example :
    QuillenStageGridLift C a ≌ Discrete (QuillenQSimplex C a) :=
  quillenStageGridQProjectionEquivalence C a

example :
    (quillenStageGridQProjectionEquivalence C a).functor =
      quillenStageGridQProjection C a := by
  simp

end ProjectionApi

section StrictFibers

variable {a : SimplexCategory} (q : QuillenQSimplex C a)

example (X Y : QuillenStageGridFiber q) : Nonempty (X ⟶ Y) :=
  quillenStageGridFiber_hom_nonempty X Y

example (X Y : QuillenStageGridFiber q) : Subsingleton (X ⟶ Y) :=
  quillenStageGridFiber_hom_subsingleton q X Y

example (X Y : QuillenStageGridFiber q) (f g : X ⟶ Y) : f = g :=
  (quillenStageGridFiber_hom_subsingleton q X Y).allEq f g

example : QuillenStageGridFiber q ≌ Discrete PUnit :=
  quillenStageGridFiberEquivalencePUnit q

end StrictFibers

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example (a : SimplexCategory) :
    QuillenStageGridLift C₀ a ≌ Discrete (QuillenQSimplex C₀ a) :=
  quillenStageGridQProjectionEquivalence C₀ a

example {a : SimplexCategory} (q : QuillenQSimplex C₀ a) :
    QuillenStageGridFiber q ≌ Discrete PUnit :=
  quillenStageGridFiberEquivalencePUnit q

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example (a : SimplexCategory) :
    QuillenStageGridLift C₁ a ≌ Discrete (QuillenQSimplex C₁ a) :=
  quillenStageGridQProjectionEquivalence C₁ a

example {a : SimplexCategory} (q : QuillenQSimplex C₁ a) :
    QuillenStageGridFiber q ≌ Discrete PUnit :=
  quillenStageGridFiberEquivalencePUnit q

end TypeOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example (a : SimplexCategory) :
    QuillenStageGridLift C₀₁ a ≌ Discrete (QuillenQSimplex C₀₁ a) :=
  quillenStageGridQProjectionEquivalence C₀₁ a

example {a : SimplexCategory} (q : QuillenQSimplex C₀₁ a) :
    QuillenStageGridFiber q ≌ Discrete PUnit :=
  quillenStageGridFiberEquivalencePUnit q

example (a : SimplexCategory) :
    QuillenStageGridLift C₁₀ a ≌ Discrete (QuillenQSimplex C₁₀ a) :=
  quillenStageGridQProjectionEquivalence C₁₀ a

example {a : SimplexCategory} (q : QuillenQSimplex C₁₀ a) :
    QuillenStageGridFiber q ≌ Discrete PUnit :=
  quillenStageGridFiberEquivalencePUnit q

end MixedUniverses

section NoGlobalInstances

variable (C) (a : SimplexCategory)

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Full

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Faithful

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).IsEquivalence

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Final

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Initial

variable (q : QuillenQSimplex C a)

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsConnected (QuillenStageGridFiber q)

end NoGlobalInstances

section Nonclaims

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridFiber_weaklyContractible

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQProjectionDiagonal_mem_realizationWeakEquivalences

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridToNQ

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridStageProjectionDiagonal

end Nonclaims

#print axioms AlgebraicKTheory.edgewiseStageVertexIndex_last
#print axioms AlgebraicKTheory.edgewiseStageQuillenSimplexFunctor_faithful
#print axioms AlgebraicKTheory.quillenStageGridLift_hom_subsingleton
#print axioms AlgebraicKTheory.quillenStageGridFiber_hom_nonempty
#print axioms AlgebraicKTheory.quillenStageGridQProjection_full
#print axioms AlgebraicKTheory.quillenStageGridQProjection_faithful
#print axioms AlgebraicKTheory.quillenStageGridQProjection_isEquivalence
#print axioms AlgebraicKTheory.quillenStageGridQProjectionEquivalence
#print axioms AlgebraicKTheory.quillenStageGridFiber_hom_subsingleton
#print axioms AlgebraicKTheory.quillenStageGridFiberEquivalencePUnit

end MathlibExtTest.KTheory.Categorical.QuillenStageGridQProjectionEquivalenceTests

end
