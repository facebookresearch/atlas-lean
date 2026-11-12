/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedOpenWalkCarrier
import Code.FrontierD.FKRectRefinedBoundaryOrbitCarrier









open Finset SimpleGraph

namespace StatMech.FrontierD

open Equiv

noncomputable section



theorem fkRect_boundaryOrbit_winding_dependent_of_openWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x : R.Vertex}
    (w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x x)
    (d : FKMedialDart R.medialTorus) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F) d))
      (fkRectWalkWinding R w) := by
  classical
  let p : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  have hp : fkRectLiftedVertex R p = x := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  obtain ⟨q, l, hq, hwlift, hlpath, hlblocks⟩ :=
    exists_fkRectRefinedOpenWalkCarrier R F w p hp
  let C : FKRectRefinedWalkCarrier R hwlift := ⟨l, hlpath⟩
  have htranslation : C.translation =
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R w)).1,
        4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R w)).2) := by
    unfold FKRectRefinedWalkCarrier.translation
    rw [hwlift.closed_develop_sub_eq_deck_winding R]
  have hzero := hlblocks.repeated_boundary_interaction_eq_zero
    R F d (orderOf (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))))
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R
        (fkRectConfigurationOfEdges R F) d))
    (fkRectWalkWinding R w)
  have hinteraction : fkRectRefinedRawInteraction
      (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R
        (fkRectConfigurationOfEdges R F) d)
      C.coverDarts = 0 := by
    unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
      fkRectCanonicalRefinedBoundaryOrbitDarts
      FKRectRefinedWalkCarrier.coverDarts
    rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
      htranslation]
    unfold fkRectSquareCoverDartList
    exact hzero
  exact
    (fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_zero_iff
      R (fkRectConfigurationOfEdges R F) d C).mp hinteraction

end

end StatMech.FrontierD
