/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerHornReplacement
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.KanWeakComparison

/-!
# The two weak classes on original groupoidal simplicial sets

The actual strict inner-horn replacement turns the original groupoidality of
both homotopy categories into Kan replacement endpoints. Its two actual units
are unconditionally categorical and realization weak equivalences. Their
original naturality square and two-out-of-three transfer Corollary 9.8 back
to the same original map, without a quasicategory hypothesis on either input.

Source: Joyal, Corollaries 9.7 and 9.8, printed p. 112.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

universe u

namespace SSet

/-- On the same original map with groupoidal intrinsic homotopy categories,
categorical weakness is equivalent to the full realization weak predicate. -/
theorem categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid
    {X Y : SSet.{u}} [IsGroupoid X.HomotopyCategory]
    [IsGroupoid Y.HomotopyCategory] (f : X ⟶ Y) :
    categoricalEquivalences f ↔ realizationWeakEquivalences f := by
  let _ : KanComplex (innerHornReplacement.obj X) :=
    innerHornReplacement_kanComplex_of_isGroupoid X
  let _ : KanComplex (innerHornReplacement.obj Y) :=
    innerHornReplacement_kanComplex_of_isGroupoid Y
  calc
    categoricalEquivalences f ↔
        categoricalEquivalences (f ≫ innerHornReplacementUnit.app Y) :=
      (categoricalEquivalences.postcomp_iff f (innerHornReplacementUnit.app Y)
        (innerHornReplacementUnit_categorical Y)).symm
    _ ↔ categoricalEquivalences
        (innerHornReplacementUnit.app X ≫ innerHornReplacement.map f) := by
      rw [innerHornReplacementUnit_naturality f]
    _ ↔ categoricalEquivalences (innerHornReplacement.map f) :=
      categoricalEquivalences.precomp_iff (innerHornReplacementUnit.app X)
        (innerHornReplacement.map f) (innerHornReplacementUnit_categorical X)
    _ ↔ realizationWeakEquivalences (innerHornReplacement.map f) :=
      categoricalEquivalences_iff_realizationWeakEquivalences_of_kanComplex
        (innerHornReplacement.map f)
    _ ↔ realizationWeakEquivalences
        (innerHornReplacementUnit.app X ≫ innerHornReplacement.map f) :=
      (realizationWeakEquivalences.precomp_iff (innerHornReplacementUnit.app X)
        (innerHornReplacement.map f) (innerHornReplacementUnit_realizationWeak X)).symm
    _ ↔ realizationWeakEquivalences
        (f ≫ innerHornReplacementUnit.app Y) := by
      rw [innerHornReplacementUnit_naturality f]
    _ ↔ realizationWeakEquivalences f :=
      realizationWeakEquivalences.postcomp_iff f (innerHornReplacementUnit.app Y)
        (innerHornReplacementUnit_realizationWeak Y)

end SSet
