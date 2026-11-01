/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Constructive finite decision procedures for compact spin certificate plans. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsFastDecision

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every edge condition is decidable by its bounded binary matrix and phase calculations. -/
instance representativeSpinEdgeDecidable (a b c : RepresentativeSpinModel) :
    Decidable (representativeSpinEdge a b c) := representativeSpinEdgeDecisionFast a b c

/-- Structural recursion decides each finite certificate plan without assuming its validity. -/
def representativeSpinPlanDecision {ι : Type} (models : ι → RepresentativeSpinModel)
    (a : RepresentativeSpinModel) (plan : RepresentativeSpinPlan ι) :
    Decidable (representativeSpinPlanValid models a plan) :=
  representativeSpinPlanDecisionFast models a plan

/-- The finite recursive procedure supplies the plan check used by kernel decision proofs. -/
instance representativeSpinPlanValidDecidable {ι : Type}
    (models : ι → RepresentativeSpinModel) (a : RepresentativeSpinModel)
    (plan : RepresentativeSpinPlan ι) : Decidable (representativeSpinPlanValid models a plan) :=
  representativeSpinPlanDecision models a plan

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
