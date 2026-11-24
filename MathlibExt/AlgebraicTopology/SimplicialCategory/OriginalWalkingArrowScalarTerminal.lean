/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectGenerators
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategory
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The SAME original walking-arrow target is scalar terminal

In every original scalar degree, the actual unit-Hom walking arrow has
one forward arrow, original identity endomorphisms and empty reverse
Hom. Its SAME target object is terminal in the canonical ScalarObject
category, retaining its actual original objects and full Hom simplices.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalWalkingArrowScalarTerminal
/-- The SAME original unit-Hom walking arrow with its actual two objects. -/
abbrev object : Carrier.{u} := BergnerTwoObject.object (𝟙_ SSet.{u})

/-- The SAME original walking-arrow target has its actual canonical scalar wrapper. -/
def target (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject object.{u} q :=
  SSet.ScalarObject.mk (BergnerTwoObject.target (𝟙_ SSet.{u}))

/-- The entire original scalar terminal arrow uses its SAME actual unit Hom simplex. -/
def toTarget (q : SimplexCategoryᵒᵖ) (x : SSet.ScalarObject object.{u} q) : x ⟶ target q := by
  cases x with
  | mk x =>
      cases x with
      | up x =>
          cases x <;> exact PUnit.unit

/-- The SAME actual original target is genuinely terminal in every canonical scalar degree. -/
def isTerminal (q : SimplexCategoryᵒᵖ) : IsTerminal (target.{u} q) :=
  IsTerminal.ofUniqueHom (toTarget q) (fun x f => by
    cases x with
    | mk x =>
        cases x with
        | up x =>
            cases x <;> change PUnit.unit = PUnit.unit
            all_goals cases f; rfl)

end CategoryTheory.SimplicialEnrichment.OriginalWalkingArrowScalarTerminal
