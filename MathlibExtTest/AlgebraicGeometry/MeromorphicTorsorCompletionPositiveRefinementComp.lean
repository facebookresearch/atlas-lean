/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementComp

/-!
# Tests for composition of positive refinement maps

The composition theorem gives the corresponding identity on completed coefficients.
Source: Fargues--Scholze,
arXiv:2102.13459v4, Sections III.3 and VI.1; Beauville--Laszlo descent.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementComp

open CategoryTheory MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundleModifications AnalyticMeromorphicCoordinates
open MeromorphicHeckeModels MeromorphicCompletionRefinements

example (p : ℕ) [Fact p.Prime] (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) (a : FormalRing p E d U Q) :
    positiveMap p E d U Q Q'' t T.powers T.finite a =
      positiveMap p E d U Q' Q'' s S.powers S.finite
        (positiveMap p E d U Q Q' r R.powers R.finite a) := by
  exact DFunLike.congr_fun
    (WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion.positiveRefinement_comp
      p E d U Q Q' Q'' r s t ht R S T) a

end MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionPositiveRefinementComp
