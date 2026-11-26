/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.HomotopyTwoCategory

/-!
# Consumers of the original homotopy two-category objects and cells
-/

noncomputable section

universe u v

open CategoryTheory
open scoped Simplicial

variable {C : Type v} [EnrichedCategory SSet.{u} C]

example : SSet.HomotopyTwoCategory C =
    CatEnriched (TransportEnrichment SSet.hoFunctor.{u} C) := rfl

example (x : C) :
    SSet.HomotopyTwoCategory.originalObject
      (SSet.HomotopyTwoCategory.objectOf x) = x := rfl

example {x y : C} (f : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    SSet.HomotopyTwoCategory.originalOneCell
      (SSet.HomotopyTwoCategory.oneCell f) = f := rfl

example {x y : C} {f g : (x ⟶[SSet.{u}] y) _⦋0⦌} (e : SSet.Edge f g) :
    SSet.HomotopyTwoCategory.oneCell f ⟶ SSet.HomotopyTwoCategory.oneCell g :=
  SSet.HomotopyTwoCategory.twoCell e
