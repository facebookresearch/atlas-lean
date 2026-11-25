/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWRetract
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Weak homotopy equivalences of spaces

This file is part of the KQ3 layer. It packages the universe-polymorphic property
`TopCat.weakHomotopyEquivalences` as the inverse image of `SSet.KanComplex.W`
along the singular-complex functor `TopCat.toSSet`, following Goerss--Jardine,
Simplicial Homotopy Theory, I.3. Only the categorical inverse-image packaging
is formalized here; no homotopy-group, groupoid, cancellation, or retract
argument is reproved. This is not a model structure, a
`CategoryWithWeakEquivalences` instance, a `ContainsIdentities` claim, or a
product-closure claim.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace TopCat

/-- Weak homotopy equivalences of spaces: maps whose singular complex lies in
`SSet.KanComplex.W`. Universe-polymorphic packaging of the KQ2 weak-equivalence class
for the KQ3 topological model-structure lane. -/
def weakHomotopyEquivalences : MorphismProperty TopCat.{u} :=
  SSet.KanComplex.W.inverseImage TopCat.toSSet.{u}

/-- Membership unfolds to the singular-complex condition. -/
theorem mem_weakHomotopyEquivalences_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    weakHomotopyEquivalences f ↔ SSet.KanComplex.W (TopCat.toSSet.map f) :=
  Iff.rfl

instance hasTwoOutOfThreeProperty : weakHomotopyEquivalences.HasTwoOutOfThreeProperty :=
  inferInstanceAs ((SSet.KanComplex.W.inverseImage TopCat.toSSet).HasTwoOutOfThreeProperty)

instance isStableUnderRetracts : weakHomotopyEquivalences.IsStableUnderRetracts :=
  inferInstanceAs ((SSet.KanComplex.W.inverseImage TopCat.toSSet).IsStableUnderRetracts)

instance respectsIso : weakHomotopyEquivalences.RespectsIso :=
  inferInstanceAs ((SSet.KanComplex.W.inverseImage TopCat.toSSet).RespectsIso)

end TopCat
