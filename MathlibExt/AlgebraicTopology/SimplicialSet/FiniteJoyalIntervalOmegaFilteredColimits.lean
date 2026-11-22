/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller
public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerFilteredColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The chosen omega attachment preserves filtered colimits

Finite stages preserve filtered colimits by their specified zero and successor
isomorphisms. The flipped stage diagram and the native colimit functor then
preserve these colimits, and their canonical natural isomorphism identifies
the result with the original chosen omega functor.

This is the finite-domain sharpening of Cisinski 2006, Proposition 1.2.35.
No fibrancy or replacement conclusion is needed for preservation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SSet.joyalInterval

private lemma stage_preservesFilteredColimits (J : Type u) [SmallCategory J] [IsFiltered J]
    (n : ℕ) : PreservesColimitsOfShape J (auxiliaryOmegaStages.{u}.obj n) := by
  have hmono : ∀ i : AuxiliaryGeneratorIndex.{u}, Mono (auxiliaryGeneratorArrow i).hom :=
    mono_auxiliaryGeneratorArrow
  let :=  hmono
  have hfinite : ∀ i : AuxiliaryGeneratorIndex.{u}, SSet.Finite (auxiliaryGeneratorArrow i).left :=
    finite_auxiliaryGeneratorArrow_source
  let :=  hfinite
  have hL₁ : PreservesFilteredColimitsOfSize.{u, u} auxiliaryFreeFiller.{u} := by
    change PreservesFilteredColimitsOfSize.{u, u}
      (labelledFreeFiller
        (fun i : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow i).hom))
    infer_instance
  let :=  hL₁
  induction n with
  | zero =>
    exact preservesColimitsOfShape_of_natIso auxiliaryOmegaStagesZeroIso.{u}.symm
  | succ n ih =>
    let :=  ih
    exact preservesColimitsOfShape_of_natIso (auxiliaryOmegaStagesSuccIso.{u} n).symm

/-- The actual chosen omega functor preserves every filtered colimit in its value universe. -/
instance auxiliaryOmegaFreeFiller_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} auxiliaryOmegaFreeFiller.{u} where
  preserves_filtered_colimits J _ _ := by
    have hflip : PreservesColimitsOfShape J auxiliaryOmegaStages.{u}.flip := by
      apply preservesColimitsOfShape_of_evaluation
      intro n
      let :=  stage_preservesFilteredColimits J n
      exact preservesColimitsOfShape_of_natIso
        (CategoryTheory.flipCompEvaluation auxiliaryOmegaStages.{u} n).symm
    let :=  hflip
    have hcolim : PreservesColimitsOfShape J
        (auxiliaryOmegaStages.{u}.flip ⋙ (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u})) := by
      infer_instance
    let :=  hcolim
    exact preservesColimitsOfShape_of_natIso
      (colimitIsoFlipCompColim auxiliaryOmegaStages.{u}).symm

end SSet.joyalInterval
