/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialBoundaryOrbitReachability
import Code.FrontierD.FKRectTorusSurfaceReduction










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedial_west_east_not_reachable_iff_forall_iterate_ne
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    (¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) ↔
      ∀ n : Nat,
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[n]
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) ≠
          fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
  rw [fkMedial_west_east_reachable_iff_exists_boundary_iterate]
  simp only [not_exists]



theorem fkRectConnectedInsertionSurfaceBridge_iff_orbitAvoidance
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectConnectedInsertionSurfaceBridge R F e r heF hold ↔
      ((∀ n : Nat,
          ((fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R
              (fkRectConfigurationOfEdges R F)))^[n]
                (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) ≠
              fkMedialEastDart (fkRectMedialVertexOfEdge R e)) ↔
        ∃ q : (fkRectOpenGraph R
            (fkRectConfigurationOfEdges R F)).Walk
              (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e),
          FKRectWindingIndependent (fkRectWalkWinding R q)
            (fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r))) := by
  unfold FKRectConnectedInsertionSurfaceBridge
  rw [fkRectMedial_west_east_not_reachable_iff_forall_iterate_ne]

end

end StatMech.FrontierD
