/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinInverse

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpinData

/-! Two complete signed multiplication edges for one genuine transporter conjugate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private instance (a b c : RepresentativeSpinModel) : Decidable (representativeSpinEdge a b c) :=
  representativeSpinEdgeDecisionFast a b c

set_option maxHeartbeats 2000000 in
-- Check all twelve-coordinate entries and diagonal/polar signs of this original product.
/-- The first original product has exactly the recorded complete signed pullback. -/
theorem generatedSixth_monomial_spin_prefix_1 :
    representativeSpinEdge (generatedSixthPermutationProfileModel 0)
      (generatedSixthMonomialSpinSource 1) (generatedSixthMonomialSpinPrefix 1) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check all twelve-coordinate entries and diagonal/polar signs of this inverse conjugation.
/-- The inverse transporter conjugation retains every original central quadratic sign. -/
theorem generatedSixth_monomial_spin_conjugate_1 :
    representativeSpinEdge (generatedSixthMonomialSpinPrefix 1)
      (generatedSixthPermutationProfileInverseModel 0) (generatedSixthMonomialSpinModel 1) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
