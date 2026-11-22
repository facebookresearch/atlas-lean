/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningParameterCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalMappingWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.WeakMonoParameterClosure

/-!
# Original critical lower-face parameter cells and their actual native images

The original critical last edge, complete outer horn, selected maximal
parameter and whole base projection are unchanged. Every such mixed
cell is actually weak in the original Cartesian source model and its
actual straightening image has the proved projective left class in the
original coherent target model. Target weakness is a further obligation.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original full critical outer-horn cell over every actual whole base projection is monic on its same marked
slice carrier. -/
theorem cartesianCriticalOver_nativeMono (B : SSet.{u}) (m : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B) :
    Mono (cartesianCriticalOver m r) := by
  have : Mono (cartesianCriticalOver m r).left := cartesianCriticalCell_mono m
  exact Over.mono_of_mono_left _

/-- Every actual original critical lower-face cell and original monic scalar parameter have a genuinely projective
native image with the unchanged critical edge, inherited marks and base map. -/
theorem nativeStraightening_criticalParameterCell_projectiveLeft (B : SSet.{u}) (m : ℕ)
    (r : cartesianCriticalTarget.{u} m ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      ((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))) := by
  have : Mono (cartesianCriticalOver m r) := cartesianCriticalOver_nativeMono B m r
  exact nativeStraightening_parameterCell_projectiveLeft B a (cartesianCriticalOver m r)

/-- The same original whole critical lower-face/parameter cell is genuinely a source Cartesian weak marked mono and
its actual unchanged native image has the target projective left class, both proved from the original models and
actual maps. -/
theorem nativeStraightening_criticalParameterCell_sourceWeak_targetProjective (B : SSet.{u}) [Quasicategory B]
    (m : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    cartesianTestingTrivialCofibrations B (overParameterPushoutProduct a (cartesianCriticalOver m r)) ∧
      (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
        ((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))) := by
  have hi : cartesianTestingTrivialCofibrations B (cartesianCriticalOver m r) :=
    ⟨cartesianCriticalOver_nativeMono B m r, cartesianCriticalOver_weak m r⟩
  exact ⟨cartesianWeakMono_parameter_closed (cartesianCriticalOver m r) hi a,
    nativeStraightening_criticalParameterCell_projectiveLeft B m r a⟩

end SSet.Marked
