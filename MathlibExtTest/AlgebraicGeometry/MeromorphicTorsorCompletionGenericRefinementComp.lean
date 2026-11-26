/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementComp

/-!
Pointwise and coefficient forms of generic refinement composition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels MeromorphicCompletionRefinements
open WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementComp

example (p : ℕ) [Fact p.Prime] (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) (x : GenericRing p E d U Q) :
    genericMap p E d U Q Q'' t T x =
      genericMap p E d U Q' Q'' s S (genericMap p E d U Q Q' r R x) := by
  rw [genericRefinement_comp p E d U Q Q' Q'' r s t ht R S T]
  rfl

example (p : ℕ) [Fact p.Prime] (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q Q' Q'' : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q') (s : PoleRefinement p E d U Q' Q'')
    (t : PoleRefinement p E d U Q Q'') (ht : t.map = s.map ≫ r.map)
    (R : CoefficientRefinement p E d U Q Q' r)
    (S : CoefficientRefinement p E d U Q' Q'' s)
    (T : CoefficientRefinement p E d U Q Q'' t) (a : FormalRing p E d U Q) :
    genericMap p E d U Q Q'' t T (algebraMap _ _ a) =
      algebraMap _ (GenericRing p E d U Q'')
        (positiveMap p E d U Q' Q'' s S.powers S.finite
          (positiveMap p E d U Q Q' r R.powers R.finite a)) := by
  rw [genericRefinement_comp p E d U Q Q' Q'' r s t ht R S T]
  simp only [RingHom.comp_apply, genericMap_coefficients]

end MathlibExtTest.AlgebraicGeometry.MeromorphicTorsorCompletionGenericRefinementComp
