/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementIdentity

/-!
# Tests for identity generic refinement

Identity generic refinement is bijective on the localized completed ring.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1;
Beauville--Laszlo descent.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementIdentity

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCompletionRefinements

private theorem genericRefinement_bijective (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    Function.Bijective (genericMap p E d U Q Q r R) := by
  rw [WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion.genericRefinement_identity
    p E d U Q r hr R]
  exact Function.bijective_id

end MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementIdentity
