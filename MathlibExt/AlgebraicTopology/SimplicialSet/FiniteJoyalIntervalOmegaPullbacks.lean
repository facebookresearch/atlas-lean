/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller
public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerPullbacks
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# The chosen omega attachment preserves pullbacks

Every chosen finite stage preserves pullbacks. Filtered-colimit exactness
of sets transfers to simplicial sets and the native flipped stage diagram.
The canonical colimit isomorphism then gives preservation by the actual
chosen omega functor, for arbitrary span maps.

This strengthens the monic-span claim in Cisinski, Construction 2.4.36
and Lemma 2.4.37, using labelled normal forms and filtered-colimit exactness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SSet.joyalInterval

private lemma stage_preservesPullbacks (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan (auxiliaryOmegaStages.{u}.obj n) := by
  have hmono : ∀ i : AuxiliaryGeneratorIndex.{u}, Mono (auxiliaryGeneratorArrow i).hom :=
    mono_auxiliaryGeneratorArrow
  let := hmono
  have hL₁ : PreservesLimitsOfShape WalkingCospan auxiliaryFreeFiller.{u} := by
    change PreservesLimitsOfShape WalkingCospan
      (labelledFreeFiller
        (fun i : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow i).hom))
    infer_instance
  let := hL₁
  induction n with
  | zero =>
    exact preservesLimitsOfShape_of_natIso auxiliaryOmegaStagesZeroIso.{u}.symm
  | succ n ih =>
    let := ih
    exact preservesLimitsOfShape_of_natIso (auxiliaryOmegaStagesSuccIso.{u} n).symm

/-- The actual chosen omega functor preserves all pullbacks, without monic span hypotheses. -/
instance auxiliaryOmegaFreeFiller_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan auxiliaryOmegaFreeFiller.{u} := by
  have hflip : PreservesLimitsOfShape WalkingCospan auxiliaryOmegaStages.{u}.flip := by
    apply preservesLimitsOfShape_of_evaluation
    intro n
    let := stage_preservesPullbacks.{u} n
    exact preservesLimitsOfShape_of_natIso
      (CategoryTheory.flipCompEvaluation auxiliaryOmegaStages.{u} n).symm
  let := hflip
  have hcolim : PreservesLimitsOfShape WalkingCospan
      (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
    infer_instance
  let := hcolim
  have hcomp : PreservesLimitsOfShape WalkingCospan
      (auxiliaryOmegaStages.{u}.flip ⋙ (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u})) := by
    infer_instance
  let := hcomp
  exact preservesLimitsOfShape_of_natIso
    (colimitIsoFlipCompColim auxiliaryOmegaStages.{u}).symm

end SSet.joyalInterval
