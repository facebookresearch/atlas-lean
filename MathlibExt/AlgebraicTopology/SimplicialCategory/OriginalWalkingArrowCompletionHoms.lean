/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWalkingArrowScalarTerminal
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionEnrichment
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidTerminalHoms
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# The SAME original walking-arrow completion has actual unit Homs

The actual target is scalar terminal in every original degree. Its full
native groupoid completion Hom is therefore nonempty and subsingleton.
The SAME actual completion Hom simplicial set maps isomorphically to the
original tensor unit, with every ordinal operator retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.OriginalWalkingArrowCompletionHoms
open ScalarGroupoidCompletion OriginalWalkingArrowScalarTerminal

/-- Every complete original walking completion Hom simplex is unique. -/
theorem hom_subsingleton (q : SimplexCategoryᵒᵖ) (x y : OriginalWalkingArrowScalarTerminal.object.{u}) :
    Subsingleton ((hom OriginalWalkingArrowScalarTerminal.object x y).obj q) :=
  FreeGroupoid.homSubsingleton (OriginalWalkingArrowScalarTerminal.target q)
    (OriginalWalkingArrowScalarTerminal.isTerminal q) _ _

/-- Every complete original walking completion Hom contains its original terminal-cone arrow. -/
theorem hom_nonempty (q : SimplexCategoryᵒᵖ) (x y : OriginalWalkingArrowScalarTerminal.object.{u}) :
    Nonempty ((hom OriginalWalkingArrowScalarTerminal.object x y).obj q) :=
  FreeGroupoid.homNonempty (OriginalWalkingArrowScalarTerminal.target q)
    (OriginalWalkingArrowScalarTerminal.isTerminal q) _ _

/-- The SAME complete original Hom-to-unit map is a genuine simplicial isomorphism. -/
def homIso (x y : OriginalWalkingArrowScalarTerminal.object.{u}) :
    hom OriginalWalkingArrowScalarTerminal.object x y ≅ 𝟙_ SSet.{u} := by
  let f := CodiscreteEnrichment.toUnit (hom OriginalWalkingArrowScalarTerminal.object x y)
  have hf (q : SimplexCategoryᵒᵖ) : IsIso (f.app q) := by
    apply (isIso_iff_bijective _).mpr
    constructor
    · let _ := hom_subsingleton q x y
      exact fun a b _ => Subsingleton.elim _ _
    · intro a
      let h := hom_nonempty q x y
      refine ⟨Classical.choice h, ?_⟩
      change PUnit.unit = a
      cases a
      rfl
  let _ : ∀ q, IsIso (f.app q) := hf
  let _ : IsIso f := NatIso.isIso_of_isIso_app f
  exact asIso f

/-- The SAME complete original Hom-to-unit map is genuinely realization weak. -/
theorem hom_toUnit_weak (x y : OriginalWalkingArrowScalarTerminal.object.{u}) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit
      (hom OriginalWalkingArrowScalarTerminal.object x y)) := by
  let _ : IsIso (CodiscreteEnrichment.toUnit (hom OriginalWalkingArrowScalarTerminal.object x y)) :=
    (homIso x y).isIso_hom
  exact SSet.realizationWeakEquivalences.of_isIso _

end CategoryTheory.SimplicialEnrichment.OriginalWalkingArrowCompletionHoms
