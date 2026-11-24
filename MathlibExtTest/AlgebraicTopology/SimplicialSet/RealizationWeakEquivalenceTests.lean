/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence

/-!
# Tests for neutral realization weak equivalences

These tests pin the property definition, membership formula, universe
polymorphism, surface containment, and standard trust without importing the
legacy identity/closure proof layer.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace MathlibExtTest.SSet.RealizationWeakEquivalence

#check @SSet.realizationWeakEquivalences
#check @SSet.mem_realizationWeakEquivalences_iff

section Generic

variable {X Y : SSet.{u}} (f : X ⟶ Y)

example : SSet.realizationWeakEquivalences f ↔
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map f)) :=
  SSet.mem_realizationWeakEquivalences_iff f

example (hf : SSet.realizationWeakEquivalences f) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map f)) := by
  exact hf

end Generic

section UniverseCorners

variable {X₀ Y₀ : SSet.{0}} (f₀ : X₀ ⟶ Y₀)
variable {X₁ Y₁ : SSet.{1}} (f₁ : X₁ ⟶ Y₁)

example : Prop := SSet.realizationWeakEquivalences f₀
example : Prop := SSet.realizationWeakEquivalences f₁

end UniverseCorners

/-- error: Unknown constant `SSet.realizationWeakEquivalences_zero_eq` -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences_zero_eq

/-- error: Unknown constant `SSet.realizationWeakEquivalences_containsIdentities` -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences_containsIdentities

#print axioms SSet.realizationWeakEquivalences
#print axioms SSet.mem_realizationWeakEquivalences_iff

end MathlibExtTest.SSet.RealizationWeakEquivalence
