/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Consumers of actual Ex∞ preservation and pullback weak equivalences

The first consumer retains all four maps of an arbitrary pullback square.
The second exercises right properness with the supplied fibration and weak
map; no homotopy-fiber comparison is a premise.
-/

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

example {A B X Y : SSet.{u}} {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) :
    IsPullback (SSet.exInfinity.map p') (SSet.exInfinity.map f')
      (SSet.exInfinity.map f) (SSet.exInfinity.map p) :=
  sq.map SSet.exInfinity

example {A B X Y : SSet.{u}} {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) [Fibration p] [WeakEquivalence f] : WeakEquivalence f' :=
  IsRightProper.weakEquivalence_of_isPullback sq

example {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.exInfinity.map p) := inferInstance

#print axioms SSet.exInfinity_preservesFiniteLimits
#print axioms SSet.modelCategoryQuillen.instFibrationExInfinityMap
#print axioms SSet.modelCategoryQuillen.instIsRightProper
