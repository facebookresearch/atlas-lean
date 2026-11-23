/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveHomotopyGroup

/-!
# A groupoid-nerve second-homotopy client

Every map out of the second homotopy type of an arbitrary groupoid nerve
is constant. Object, Hom and target universes remain independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v w

namespace SSet

/-- Every target-valued map from the actual nerve second homotopy type is constant. -/
theorem groupoidNerve_piTwo_map_constant_test (C : Type u) [Groupoid.{v} C]
    (x : CategoryTheory.nerve C _⦋0⦌) (T : Type w)
    (f : SSet.KanComplex.π 2 (CategoryTheory.nerve C) x → T) : f = fun _ => f 1 := by
  let _ := piTwo_nerve_subsingleton C x
  funext a
  exact congrArg f (Subsingleton.elim a 1)

end SSet

end
