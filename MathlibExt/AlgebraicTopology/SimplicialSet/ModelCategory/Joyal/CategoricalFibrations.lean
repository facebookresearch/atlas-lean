/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences

/-! # Joyal categorical fibrations

`SSet.categoricalFibrations` is the right lifting class of monic weak
categorical equivalences. These are the fibrations of the Joyal model
structure, whose cofibrations are monomorphisms and whose weak equivalences
are `SSet.categoricalEquivalences`.

The membership criterion states the lifting property explicitly. The
identity/composition, isomorphism, retract, and base-change properties come
from the general API for right lifting classes.

The separate property `SSet.innerIsoFibrations` records inner fibrancy and
isofibrancy on homotopy categories. The usual identification with that
property requires a quasicategory codomain; Campbell's counterexample
refutes the unrestricted identification.

## References

* J. Lurie, *Higher Topos Theory*, Theorem 2.2.5.1 (the Joyal model
  structure) and Proposition 2.2.5.8 (the weak categorical equivalences).
* J. Lurie, *Higher Topos Theory*, Corollary 2.4.6.5 (the fibration
  criterion with a quasicategory codomain).
* A. Campbell, *A counterexample in quasi-category theory*,
  arXiv:1904.04965v3, Corollary 2.6.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/-- The genuine Joyal fibration class: maps having the right lifting
property against every monic weak categorical equivalence. -/
def categoricalFibrations : MorphismProperty SSet.{u} :=
  (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u}).rlp

variable {X Y : SSet.{u}}

/-- A map is a categorical fibration exactly when it lifts against every
monomorphism which is a categorical equivalence. -/
theorem categoricalFibrations.mem_iff (p : X ⟶ Y) :
    categoricalFibrations p ↔
      ∀ {A B : SSet.{u}} (i : A ⟶ B),
        Mono i → categoricalEquivalences i → HasLiftingProperty i p := by
  constructor
  · intro h A B i hi hw
    exact h i ⟨hi, hw⟩
  · intro h A B i hi
    exact h i hi.1 hi.2

/-- Categorical fibrations contain identities and are stable under composition. -/
instance categoricalFibrations.isMultiplicative :
    categoricalFibrations.{u}.IsMultiplicative :=
  inferInstanceAs ((MorphismProperty.monomorphisms SSet.{u} ⊓
    categoricalEquivalences.{u}).rlp.IsMultiplicative)

/-- Categorical fibrations are stable under retracts. -/
instance categoricalFibrations.isStableUnderRetracts :
    categoricalFibrations.{u}.IsStableUnderRetracts :=
  inferInstanceAs ((MorphismProperty.monomorphisms SSet.{u} ⊓
    categoricalEquivalences.{u}).rlp.IsStableUnderRetracts)

/-- Categorical fibrations are stable under arbitrary base change. -/
instance categoricalFibrations.isStableUnderBaseChange :
    categoricalFibrations.{u}.IsStableUnderBaseChange :=
  inferInstanceAs ((MorphismProperty.monomorphisms SSet.{u} ⊓
    categoricalEquivalences.{u}).rlp.IsStableUnderBaseChange)

/-- Categorical fibrations respect isomorphisms. -/
instance categoricalFibrations.respectsIso :
    categoricalFibrations.{u}.RespectsIso :=
  inferInstanceAs ((MorphismProperty.monomorphisms SSet.{u} ⊓
    categoricalEquivalences.{u}).rlp.RespectsIso)

end SSet
