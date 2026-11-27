/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatchingFunctor
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatchingIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingFunctor
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingIso
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Degreewise Reedy morphism properties
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The morphism property whose relative latching maps lie in `P`. -/
def reedyLeft (P : MorphismProperty C)
    [HasPushouts C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C] :
    MorphismProperty (SimplicialObject C) :=
  fun _ _ f => ∀ n : ℕ, P (relativeLatchingMap f n)

@[simp]
theorem reedyLeft_iff (P : MorphismProperty C)
    [HasPushouts C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    reedyLeft P f ↔ ∀ n : ℕ, P (relativeLatchingMap f n) :=
  Iff.rfl

/-- The morphism property whose relative matching maps lie in `P`. -/
def reedyRight (P : MorphismProperty C)
    [HasPullbacks C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C] :
    MorphismProperty (SimplicialObject C) :=
  fun _ _ f => ∀ n : ℕ, P (relativeMatchingMap f n)

@[simp]
theorem reedyRight_iff (P : MorphismProperty C)
    [HasPullbacks C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    reedyRight P f ↔ ∀ n : ℕ, P (relativeMatchingMap f n) :=
  Iff.rfl

instance (P : MorphismProperty C)
    [HasPushouts C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
    [P.ContainsIdentities] [P.RespectsIso] :
    (reedyLeft P).ContainsIdentities where
  id_mem X n :=
    (P.arrow_mk_iso_iff
      (relativeLatchingMapIdArrowIso X n)).2
      (P.id_mem (X.obj (op ⦋n⦌)))

instance (P : MorphismProperty C)
    [HasPullbacks C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
    [P.ContainsIdentities] [P.RespectsIso] :
    (reedyRight P).ContainsIdentities where
  id_mem X n :=
    (P.arrow_mk_iso_iff
      (relativeMatchingMapIdArrowIso X n)).2
      (P.id_mem (X.obj (op ⦋n⦌)))

end CategoryTheory.SimplicialObject
