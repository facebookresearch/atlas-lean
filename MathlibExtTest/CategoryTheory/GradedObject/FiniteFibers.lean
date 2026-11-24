/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import MathlibExt.CategoryTheory.GradedObject.FiniteFibers
public import MathlibExt.CategoryTheory.GradedObject.Preadditive

/-! Client tests for finite-fiber pushforward of graded objects. -/

@[expose] public section

namespace CategoryTheory.GradedObject

open Limits

universe w w' v u

variable {I : Type w} {J : Type w'} {C : Type u} [Category.{v} C]

example (X : GradedObject I C) (p : I → J) [FiniteFibers p]
    [HasFiniteCoproducts C] : X.HasMap p :=
  inferInstance

example (p : I → J) [FiniteFibers p] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] [HasFiniteLimits C] :
    PreservesFiniteLimits (map C p) :=
  inferInstance

example (p : I → J) [FiniteFibers p] [HasFiniteColimits C] :
    PreservesFiniteColimits (map C p) :=
  inferInstance

example {I J : Type} (p : I → J) :
    PreservesFiniteLimits (map AddCommGrpCat.{u} p) :=
  inferInstance

example (β : Type) :
    PreservesFiniteLimits (total β AddCommGrpCat.{u}) :=
  inferInstance

example (β : Type) :
    PreservesFiniteColimits (total β AddCommGrpCat.{u}) :=
  inferInstance

#check CategoryTheory.GradedObject.gradedObjectPreadditive
#check CategoryTheory.GradedObject.gradedObjectTotalAdditive
#check CategoryTheory.GradedObject.FiniteFibers
#check CategoryTheory.GradedObject.hasMap_of_finiteFibers
#check CategoryTheory.GradedObject.mapCompEvalIso
#check CategoryTheory.GradedObject.preservesFiniteLimits_map_of_finiteFibers
#check CategoryTheory.GradedObject.preservesFiniteColimits_map_of_finiteFibers
#check CategoryTheory.GradedObject.total_preservesFiniteLimits_of_exact
#check CategoryTheory.GradedObject.total_preservesFiniteColimits

#print axioms CategoryTheory.GradedObject.mapCompEvalIso
#print axioms CategoryTheory.GradedObject.preservesFiniteLimits_map_of_finiteFibers
#print axioms CategoryTheory.GradedObject.preservesFiniteColimits_map_of_finiteFibers
#print axioms CategoryTheory.GradedObject.total_preservesFiniteLimits_of_exact
#print axioms CategoryTheory.GradedObject.total_preservesFiniteColimits

end CategoryTheory.GradedObject
