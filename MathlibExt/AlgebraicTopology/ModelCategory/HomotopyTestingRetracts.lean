/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingTwoOutOfThree

/-!
# Arrow retracts of chosen-cylinder testing equivalences

The actual testing class is an intersection over every naive fibrant
target. Each member is pulled back from isomorphisms through the native
class presheaf and then transported from the opposite category. Native
functor, opposite and isomorphism retract closure therefore apply targetwise.

This is the retract-closure assertion of Cisinski Remark 2.4.21
(July 30, 2026 version). It needs only the specified functorial precylinder,
explicit anodyne class and terminal object, with no model-category or
source/target fibrancy premise.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
  (An : MorphismProperty C) [HasTerminal C]

/-- The actual testing class is stable under arbitrary retracts in the arrow category. -/
instance testingEquivalences.isStableUnderRetracts :
    (P.testingEquivalences An).IsStableUnderRetracts where
  of_retract h hg := by
    rw [P.testingEquivalences_eq_iInf_isomorphisms An] at hg ⊢
    rw [MorphismProperty.iInf_iff] at hg ⊢
    exact fun T ↦ MorphismProperty.of_retract h (hg T)

end HomotopicalAlgebra.Precylinder
