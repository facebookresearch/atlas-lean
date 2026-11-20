/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectConnectedInsertionOrbitReduction
import Code.FrontierD.FKRectEssentialClusterBoundary
import Code.FrontierD.FKRectRefinedInteractionCore









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section




theorem fkRectConnectedInsertionSurfaceBridge_of_boundaryTopology
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hseparated :
      ¬ (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).Reachable
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) →
        FKRectWindingIndependent
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R
              (fkRectConfigurationOfEdges R F)
              (fkMedialWestDart (fkRectMedialVertexOfEdge R e))))
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)))
    (hsame :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).Reachable
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) →
        ∀ d : FKMedialDart R.medialTorus,
          ¬ FKRectWindingIndependent
            (fkRectWalkWinding R
              (fkRectMedialBoundaryPrimalOrbitWalk R
                (fkRectConfigurationOfEdges R F) d))
            (fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r)))
    (hessential :
      ∀ q : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk
            (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e),
        fkRectWalkWinding R q ≠ (0, 0) →
          ∃ d : FKMedialDart R.medialTorus,
            (fkRectOpenGraph R
              (fkRectConfigurationOfEdges R F)).Reachable
                (fkRectMedialWestPrimal R e)
                (fkRectMedialDartPrimalLabel R d) ∧
              fkRectWalkWinding R
                (fkRectMedialBoundaryPrimalOrbitWalk R
                  (fkRectConfigurationOfEdges R F) d) ≠ (0, 0)) :
    FKRectConnectedInsertionSurfaceBridge R F e r heF hold := by
  unfold FKRectConnectedInsertionSurfaceBridge
  constructor
  · intro hnotReachable
    let w := fkRectMedialBoundaryPrimalOrbitWalk R
      (fkRectConfigurationOfEdges R F)
      (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
    let q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk
          (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e) :=
      w.copy
        (fkRectMedialDartPrimalLabel_west_vertexOfEdge R e)
        (fkRectMedialDartPrimalLabel_west_vertexOfEdge R e)
    refine ⟨q, ?_⟩
    rw [show fkRectWalkWinding R q = fkRectWalkWinding R w by
      exact fkRectWalkWinding_copy R w _ _]
    exact hseparated hnotReachable
  · rintro ⟨q, hqFundamental⟩ hreachable
    have hqne : fkRectWalkWinding R q ≠ (0, 0) := by
      intro hqzero
      apply hqFundamental
      rw [hqzero]
      norm_num [FKRectWindingIndependent]
    obtain ⟨d, hxd, hdne⟩ := hessential q hqne
    let bd := fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R
        (fkRectConfigurationOfEdges R F) d)
    have hbdq : ¬ FKRectWindingIndependent bd
        (fkRectWalkWinding R q) := by
      dsimp [bd]
      exact fkRect_boundaryOrbit_winding_dependent_of_not_hasNet
        R (fkRectConfigurationOfEdges R F)
        (fkRectMedialWestPrimal R e) q hold d hxd
    have hqbd : ¬ FKRectWindingIndependent
        (fkRectWalkWinding R q) bd := by
      intro h
      exact hbdq ((fkRectWindingIndependent_comm _ _).mp h)
    have hbdf : ¬ FKRectWindingIndependent bd
        (fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)) := by
      dsimp [bd]
      exact hsame hreachable d
    exact (not_windingIndependent_trans_of_middle_ne_zero
      (fkRectWalkWinding R q) bd
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) hdne hqbd hbdf)
      hqFundamental

end




theorem fkRectConnectedInsertionSurfaceBridge_of_localBoundaryTopology
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hseparated :
      ¬ (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).Reachable
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) →
        FKRectWindingIndependent
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R
              (fkRectConfigurationOfEdges R F)
              (fkMedialWestDart (fkRectMedialVertexOfEdge R e))))
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)))
    (hsame :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).Reachable
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) →
        ∀ d : FKMedialDart R.medialTorus,
          (fkRectOpenGraph R
            (fkRectConfigurationOfEdges R F)).Reachable
              (fkRectMedialWestPrimal R e)
              (fkRectMedialDartPrimalLabel R d) →
          fkRectWalkWinding R
              (fkRectMedialBoundaryPrimalOrbitWalk R
                (fkRectConfigurationOfEdges R F) d) ≠ (0, 0) →
          ¬ FKRectWindingIndependent
            (fkRectWalkWinding R
              (fkRectMedialBoundaryPrimalOrbitWalk R
                (fkRectConfigurationOfEdges R F) d))
            (fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r)))
    (hessential :
      ∀ q : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk
            (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e),
        fkRectWalkWinding R q ≠ (0, 0) →
          ∃ d : FKMedialDart R.medialTorus,
            (fkRectOpenGraph R
              (fkRectConfigurationOfEdges R F)).Reachable
                (fkRectMedialWestPrimal R e)
                (fkRectMedialDartPrimalLabel R d) ∧
              fkRectWalkWinding R
                (fkRectMedialBoundaryPrimalOrbitWalk R
                  (fkRectConfigurationOfEdges R F) d) ≠ (0, 0)) :
    FKRectConnectedInsertionSurfaceBridge R F e r heF hold := by
  unfold FKRectConnectedInsertionSurfaceBridge
  constructor
  · intro hnotReachable
    let w := fkRectMedialBoundaryPrimalOrbitWalk R
      (fkRectConfigurationOfEdges R F)
      (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
    let q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk
          (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e) :=
      w.copy
        (fkRectMedialDartPrimalLabel_west_vertexOfEdge R e)
        (fkRectMedialDartPrimalLabel_west_vertexOfEdge R e)
    refine ⟨q, ?_⟩
    rw [show fkRectWalkWinding R q = fkRectWalkWinding R w by
      exact fkRectWalkWinding_copy R w _ _]
    exact hseparated hnotReachable
  · rintro ⟨q, hqFundamental⟩ hreachable
    have hqne : fkRectWalkWinding R q ≠ (0, 0) := by
      intro hqzero
      apply hqFundamental
      rw [hqzero]
      norm_num [FKRectWindingIndependent]
    obtain ⟨d, hxd, hdne⟩ := hessential q hqne
    let bd := fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R
        (fkRectConfigurationOfEdges R F) d)
    have hbdq : ¬ FKRectWindingIndependent bd
        (fkRectWalkWinding R q) := by
      dsimp [bd]
      exact fkRect_boundaryOrbit_winding_dependent_of_not_hasNet
        R (fkRectConfigurationOfEdges R F)
        (fkRectMedialWestPrimal R e) q hold d hxd
    have hqbd : ¬ FKRectWindingIndependent
        (fkRectWalkWinding R q) bd := by
      intro h
      exact hbdq ((fkRectWindingIndependent_comm _ _).mp h)
    have hbdf : ¬ FKRectWindingIndependent bd
        (fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)) := by
      dsimp [bd]
      exact hsame hreachable d hxd hdne
    exact (not_windingIndependent_trans_of_middle_ne_zero
      (fkRectWalkWinding R q) bd
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) hdne hqbd hbdf)
      hqFundamental

end StatMech.FrontierD
