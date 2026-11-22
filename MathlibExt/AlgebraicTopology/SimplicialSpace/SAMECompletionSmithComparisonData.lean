/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionUnitData

/-!
# A common target for diagonal completion and Smith replacement

The diagonal completion and Smith replacement are related by a commuting natural square of their
units, with the Smith replacement of the completion as a common complete Segal target. The Smith
unit and the map from the completion to this common target are Rezk weak for every input.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace SimplicialSpace.RezkCompletionSmithComparison

/-- The original object is the common source of the two actual units. -/
def spanLeft : 𝟭 SimplicialSpace.{u} ⟶ RezkCompletionData.completion := RezkCompletionData.unit

/-- The original full-E Smith replacement unit forms the second span leg. -/
def spanRight : 𝟭 SimplicialSpace.{u} ⟶ OriginalSmithCSS.replacement := OriginalSmithCSS.unit

/-- A common complete target uses the real Smith R applied to the SAME completion. -/
def commonTarget : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  RezkCompletionData.completion ⋙ OriginalSmithCSS.replacement

/-- Apply the full-E Smith unit after SAME completion to reach the common target. -/
def completionToCommon : RezkCompletionData.completion ⟶ commonTarget :=
  Functor.whiskerLeft RezkCompletionData.completion OriginalSmithCSS.unit

/-- Apply the SAME unit before full-E Smith replacement to reach the common target. -/
def smithToCommon : OriginalSmithCSS.replacement ⟶ commonTarget :=
  Functor.whiskerRight RezkCompletionData.unit OriginalSmithCSS.replacement

/-- The common-target square is the actual Smith-unit naturality at the original unit. -/
theorem commonTarget_square (W : SimplicialSpace.{u}) :
    spanLeft.app W ≫ completionToCommon.app W =
      spanRight.app W ≫ smithToCommon.app W :=
  OriginalSmithCSS.unit_naturality (RezkCompletionData.unit.app W)

theorem commonTarget_completeSegal (W : SimplicialSpace.{u}) :
    completeSegalSpaces (commonTarget.obj W) :=
  OriginalSmithCSS.replacement_completeSegal (RezkCompletionData.completion.obj W)

theorem spanRight_rezkWeak (W : SimplicialSpace.{u}) :
    rezkWeakEquivalences (spanRight.app W) := OriginalSmithCSS.unit_rezkWeak W

theorem completionToCommon_rezkWeak (W : SimplicialSpace.{u}) :
    rezkWeakEquivalences (completionToCommon.app W) :=
  OriginalSmithCSS.unit_rezkWeak (RezkCompletionData.completion.obj W)

/-- Both natural spans keep every original source/target map. -/
theorem span_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f ≫ spanLeft.app V = spanLeft.app W ≫ RezkCompletionData.completion.map f ∧
      f ≫ spanRight.app V = spanRight.app W ≫ OriginalSmithCSS.replacement.map f :=
  ⟨RezkCompletionData.unit_naturality f, OriginalSmithCSS.unit_naturality f⟩

end SimplicialSpace.RezkCompletionSmithComparison
