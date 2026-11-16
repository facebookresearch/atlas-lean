/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinitySFunctorMaps
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Whole coherent constant families and their native evaluation maps

These are the cartesian closed maps of the actual simplicial functor
category. They act on every parameter simplex and every index arrow.
They supply the fixed coherent families for native suspension and
countable-coproduct constructions.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeDiagramFamilies

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u

/-- The actual constant-diagram functor, with the original whole parameter simplex. -/
def constantFamily (X C : SSet.{u}) : C ⟶ mapping X C :=
  MonoidalClosed.curry (CartesianMonoidalCategory.snd X C)

/-- Evaluation at an actual source index vertex retains every parameter arrow. -/
def evaluateAt (X C : SSet.{u}) (x : X _⦋0⦌) : mapping X C ⟶ C :=
  (λ_ (mapping X C)).inv ≫
    (SSet.unitHomEquiv X).symm x ▷ mapping X C ≫
    MonoidalClosed.uncurry (𝟙 (mapping X C))

end MathlibExt.AlgebraicTopology.NativeDiagramFamilies
