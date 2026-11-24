/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module


public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import Mathlib.AlgebraicTopology.SingularSet

/-!
# Realization-based weak equivalences of simplicial sets

A morphism of simplicial sets is a realization weak equivalence when its
geometric realization, followed by singularization, lies in
`SSet.KanComplex.W`. This neutral provider defines only the property and its
membership formula; closure properties live in the model-category layer.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/-- A morphism of simplicial sets is a realization weak equivalence when its
image under realization followed by singularization lies in `KanComplex.W`. -/
def realizationWeakEquivalences : MorphismProperty SSet.{u} :=
  KanComplex.W.inverseImage (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})

/-- Membership in `realizationWeakEquivalences` unfolds to `KanComplex.W` for
the singularization of the realized map. -/
@[simp]
theorem mem_realizationWeakEquivalences_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences f ↔
      KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f)) :=
  Iff.rfl

end SSet
