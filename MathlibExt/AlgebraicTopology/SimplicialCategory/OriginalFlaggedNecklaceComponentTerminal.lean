/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklacePairedLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceFlankingWeak
import Mathlib.CategoryTheory.ConnectedComponents
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# Actual terminality of original nondegenerate flagged components

An actual flanked, totally nondegenerate original necklace is terminal
in its genuine original connected component. All maps are the SAME
original flagged maps, obtained by genuine paired-surjection descent.
The component nerve projection is therefore weak. Existence of such a
representative in EVERY component is a separate construction.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open Flanking

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Every original flanked object connected to a genuine nondegenerate target has an actual map to it. -/
theorem totallyNondegenerate_hom_of_zigzag (T S : Flanked K x y q)
    (hND : TotallyNondegenerate T.obj) (h : Zigzag S T) : Nonempty (S ⟶ T) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨𝟙 T⟩
  | @head S U hSU hUT ih =>
    obtain ⟨l⟩ := ih
    change Nonempty (S ⟶ U) ∨ Nonempty (U ⟶ S) at hSU
    rcases hSU with hf | hg
    · obtain ⟨f⟩ := hf
      exact ⟨f ≫ l⟩
    · obtain ⟨g⟩ := hg
      exact ⟨ObjectProperty.homMk
        (pairedLift l.hom g.hom U.property T.property S.property hND)⟩

/-- The SAME genuine nondegenerate object in its actual original component. -/
def componentTarget (T : Flanked K x y q) : (ConnectedComponents.mk T).Component :=
  ⟨T, rfl⟩

/-- The actual map from every object of the SAME original component to its nondegenerate target. -/
def componentToTarget (T : Flanked K x y q) (hND : TotallyNondegenerate T.obj)
    (S : (ConnectedComponents.mk T).Component) : S ⟶ componentTarget T :=
  ObjectProperty.homMk (Classical.choice
    (totallyNondegenerate_hom_of_zigzag T S.obj hND (Quotient.exact' S.property)))

/-- The entire original component map to its SAME nondegenerate target is unique. -/
theorem componentToTarget_unique (T : Flanked K x y q) (hND : TotallyNondegenerate T.obj)
    (S : (ConnectedComponents.mk T).Component) (f : S ⟶ componentTarget T) :
    f = componentToTarget T hND S := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact totallyNondegenerate_map_unique f.hom.hom (componentToTarget T hND S).hom.hom
    S.obj.property T.property hND

/-- The SAME genuine original nondegenerate object is terminal in its actual original component. -/
def componentTargetIsTerminal (T : Flanked K x y q) (hND : TotallyNondegenerate T.obj) :
    IsTerminal (componentTarget T) :=
  IsTerminal.ofUniqueHom (componentToTarget T hND) (componentToTarget_unique T hND)

/-- The actual point projection of this original nondegenerate component nerve is genuinely weak. -/
theorem componentNerveProjection_weak (T : Flanked K x y q) (hND : TotallyNondegenerate T.obj) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (nerve (ConnectedComponents.mk T).Component : SSet.{u})) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal
    (componentTargetIsTerminal T hND)

/-- Every SAME original flanked object in this actual component has an original map to the target. -/
theorem componentToTarget_map (T : Flanked K x y q) (hND : TotallyNondegenerate T.obj)
    (S : (ConnectedComponents.mk T).Component) :
    Nonempty (S.obj.obj ⟶ T.obj) := ⟨(componentToTarget T hND S).hom.hom⟩

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
