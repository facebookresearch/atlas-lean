/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementIdentity

/-!
# Bijectivity of identity positive refinement

The identity theorem implies that the completed coefficient map is bijective.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementIdentity

open CategoryTheory
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundleModifications AnalyticMeromorphicCoordinates
open MeromorphicCompletionRefinements

example (p : ℕ) [Fact p.Prime] (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    Function.Bijective (positiveMap p E d U Q Q r R.powers R.finite) := by
  rw [WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion.positiveRefinement_identity
    p E d U Q r hr R]
  exact Function.bijective_id

end MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementIdentity
