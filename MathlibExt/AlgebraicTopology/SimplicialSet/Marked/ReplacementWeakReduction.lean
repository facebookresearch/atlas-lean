/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FullTestingTargetRecognition
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Original replacement maps retain and detect the same full weak class

The original natural units are now proved weak. Their same naturality
square and native two-out-of-three show that the actual replacement
functors preserve and reflect mapping weakness. Full terminal testing
also gives a chosen strict extension across any original weak marked
mono into the same native replacement target, with its original unit
triangle and proved weakness.

These are actual map and testing reductions. Accessibility of the
replacement is not used as a substitute for a uniform-rank theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked

local instance replacementReductionCartesianTwoOutOfThree (B : SSet.{u}) : (cartesianWeakEquivalences
  B).HasTwoOutOfThreeProperty :=
  cartesianWeakEquivalences_hasTwoOutOfThreeProperty B
local instance replacementReductionCocartesianTwoOutOfThree (B : SSet.{u}) : (cocartesianWeakEquivalences
  B).HasTwoOutOfThreeProperty :=
  cocartesianWeakEquivalences_hasTwoOutOfThreeProperty B

/-- The actual original Cartesian replacement preserves and reflects exactly the original full mapping weak class. -/
theorem cartesianFixedBaseReplacement_map_weak_iff {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    cartesianWeakEquivalences B ((cartesianFixedBaseReplacementFunctor B).map f) ↔
      cartesianWeakEquivalences B f := by
  let η := cartesianFixedBaseReplacementUnit B
  let R := cartesianFixedBaseReplacementFunctor B
  have hX : cartesianWeakEquivalences B (η.app X) := (cartesianFixedBaseReplacementUnit_weak B X).2
  have hY : cartesianWeakEquivalences B (η.app Y) := (cartesianFixedBaseReplacementUnit_weak B Y).2
  have heq : η.app X ≫ R.map f = f ≫ η.app Y := (η.naturality f).symm
  have hbridge : cartesianWeakEquivalences B (η.app X ≫ R.map f) ↔ cartesianWeakEquivalences B (f ≫ η.app Y) :=
    (congrArg (fun g : X ⟶ R.obj Y => cartesianWeakEquivalences B g) heq).to_iff
  exact ((cartesianWeakEquivalences B).precomp_iff (W' := cartesianWeakEquivalences B) (η.app X) (R.map f)
    hX).symm.trans
    (hbridge.trans ((cartesianWeakEquivalences B).postcomp_iff (W' := cartesianWeakEquivalences B) f (η.app Y) hY))

/-- The same original dual naturality square preserves and reflects the full cocartesian weak class. -/
theorem cocartesianFixedBaseReplacement_map_weak_iff {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    cocartesianWeakEquivalences B ((cocartesianFixedBaseReplacementFunctor B).map f) ↔
      cocartesianWeakEquivalences B f := by
  let η := cocartesianFixedBaseReplacementUnit B
  let R := cocartesianFixedBaseReplacementFunctor B
  have hX : cocartesianWeakEquivalences B (η.app X) := (cocartesianFixedBaseReplacementUnit_weak B X).2
  have hY : cocartesianWeakEquivalences B (η.app Y) := (cocartesianFixedBaseReplacementUnit_weak B Y).2
  have heq : η.app X ≫ R.map f = f ≫ η.app Y := (η.naturality f).symm
  have hbridge : cocartesianWeakEquivalences B (η.app X ≫ R.map f) ↔ cocartesianWeakEquivalences B (f ≫ η.app Y) :=
    (congrArg (fun g : X ⟶ R.obj Y => cocartesianWeakEquivalences B g) heq).to_iff
  exact ((cocartesianWeakEquivalences B).precomp_iff (W' := cocartesianWeakEquivalences B) (η.app X) (R.map
    f) hX).symm.trans
    (hbridge.trans ((cocartesianWeakEquivalences B).postcomp_iff (W' := cocartesianWeakEquivalences B) f (η.app Y) hY))

private theorem cartesianReplacementExtensionSquare {B : SSet.{u}}
    {X Y : Over (max B)} (u : X ⟶ Y) :
    CommSq ((cartesianFixedBaseReplacementUnit B).app X) u
      (Over.mkIdTerminal.from ((cartesianFixedBaseReplacementFunctor B).obj X))
      (Over.mkIdTerminal.from Y) := ⟨Over.mkIdTerminal.hom_ext _ _⟩

/-- A full original weak marked mono has a chosen strict extension of the same native Cartesian unit into
  its actual replacement target. -/
def cartesianReplacementExtension {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (u : X ⟶ Y) (hu : cartesianTestingTrivialCofibrations B u) :
    Y ⟶ (cartesianFixedBaseReplacementFunctor B).obj X := by
  let s := cartesianReplacementExtensionSquare u
  let h : HasLiftingProperty u (Over.mkIdTerminal.from ((cartesianFixedBaseReplacementFunctor B).obj X)) :=
    cartesianFixedBaseReplacement_full_testing X u hu
  let _ : s.HasLift := h.sq_hasLift s
  exact s.lift

/-- The chosen extension keeps exactly the original whole unit triangle. -/
theorem cartesianReplacementExtension_fac {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (u : X ⟶ Y) (hu : cartesianTestingTrivialCofibrations B u) :
    u ≫ cartesianReplacementExtension u hu = (cartesianFixedBaseReplacementUnit B).app X := by
  let s := cartesianReplacementExtensionSquare u
  let h : HasLiftingProperty u (Over.mkIdTerminal.from ((cartesianFixedBaseReplacementFunctor B).obj X)) :=
    cartesianFixedBaseReplacement_full_testing X u hu
  let _ : s.HasLift := h.sq_hasLift s
  change u ≫ s.lift = (cartesianFixedBaseReplacementUnit B).app X
  exact s.fac_left

/-- The same strict comparison map is genuinely weak, by its original unit triangle and two-out-of-three. -/
theorem cartesianReplacementExtension_weak {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (u : X ⟶ Y) (hu : cartesianTestingTrivialCofibrations B u) :
    cartesianWeakEquivalences B (cartesianReplacementExtension u hu) :=
  (cartesianWeakEquivalences B).of_precomp u _ hu.2
    ((cartesianReplacementExtension_fac u hu).symm ▸ (cartesianFixedBaseReplacementUnit_weak B X).2)

private theorem cocartesianReplacementExtensionSquare {B : SSet.{u}}
    {X Y : Over (max B)} (u : X ⟶ Y) :
    CommSq ((cocartesianFixedBaseReplacementUnit B).app X) u
      (Over.mkIdTerminal.from ((cocartesianFixedBaseReplacementFunctor B).obj X))
      (Over.mkIdTerminal.from Y) := ⟨Over.mkIdTerminal.hom_ext _ _⟩

/-- A full original weak marked mono has a chosen strict extension of the same native Cocartesian unit into
  its actual replacement target. -/
def cocartesianReplacementExtension {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (u : X ⟶ Y) (hu : cocartesianTestingTrivialCofibrations B u) :
    Y ⟶ (cocartesianFixedBaseReplacementFunctor B).obj X := by
  let s := cocartesianReplacementExtensionSquare u
  let h : HasLiftingProperty u (Over.mkIdTerminal.from ((cocartesianFixedBaseReplacementFunctor B).obj X)) :=
    cocartesianFixedBaseReplacement_full_testing X u hu
  let _ : s.HasLift := h.sq_hasLift s
  exact s.lift

/-- The chosen extension keeps exactly the original whole unit triangle. -/
theorem cocartesianReplacementExtension_fac {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (u : X ⟶ Y) (hu : cocartesianTestingTrivialCofibrations B u) :
    u ≫ cocartesianReplacementExtension u hu = (cocartesianFixedBaseReplacementUnit B).app X := by
  let s := cocartesianReplacementExtensionSquare u
  let h : HasLiftingProperty u (Over.mkIdTerminal.from ((cocartesianFixedBaseReplacementFunctor B).obj X)) :=
    cocartesianFixedBaseReplacement_full_testing X u hu
  let _ : s.HasLift := h.sq_hasLift s
  change u ≫ s.lift = (cocartesianFixedBaseReplacementUnit B).app X
  exact s.fac_left

/-- The same strict comparison map is genuinely weak, by its original unit triangle and two-out-of-three. -/
theorem cocartesianReplacementExtension_weak {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} (u : X ⟶ Y) (hu : cocartesianTestingTrivialCofibrations B u) :
    cocartesianWeakEquivalences B (cocartesianReplacementExtension u hu) :=
  (cocartesianWeakEquivalences B).of_precomp u _ hu.2
    ((cocartesianReplacementExtension_fac u hu).symm ▸ (cocartesianFixedBaseReplacementUnit_weak B X).2)

end SSet.Marked
