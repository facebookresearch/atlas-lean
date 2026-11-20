/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectConnectedInsertionCharge



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section





theorem fkRectFirstEssentialInsertion_newBoundaryOrbit_ne_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (htrivial : ∀ (x : R.Vertex)
      (p : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk x x),
        fkRectWalkWinding R p = (0, 0))
    (hfund : fkRectWalkWinding R
      (fkRectInsertedFundamentalWalk R F e r) ≠ (0, 0)) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R (insert e F))
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1) ≠
      (0, 0) := by
  let oldPairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let d := (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1
  have hmedial : (fkMedialLoopGraph R.medialTorus oldPairing).Reachable
      (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
      (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
    by_contra hsep
    have hsurface :=
      fkRectConnectedInsertionSurfaceBridge_unconditional
        R F e r heF hold
    obtain ⟨q, hq⟩ := hsurface.mp hsep
    apply hq
    rw [htrivial]
    simp
  let w := fkRectMedialBoundaryPrimalOrbitWalk R
    (fkRectConfigurationOfEdges R (insert e F)) d
  have hcharge : fkRectInsertedEdgeCharge R e w ≠ 0 := by
    exact fkRectInsertedEdgeCharge_newBoundaryOrbit_ne_zero_of_reachable
      R F e heF hmedial
  obtain ⟨q, hdecomp⟩ :=
    fkRectWalkWinding_insert_eq_old_add_charge R F e r heF w
  have hqzero : fkRectWalkWinding R q = (0, 0) := htrivial _ q
  rw [hqzero] at hdecomp
  change fkRectWalkWinding R w =
    (0 : Int × Int) + fkRectInsertedEdgeCharge R e w •
      fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) at hdecomp
  have hdecomp' : fkRectWalkWinding R w =
      fkRectInsertedEdgeCharge R e w •
        fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) := by
    simpa only [zero_add] using hdecomp
  intro hzero
  change fkRectWalkWinding R w = (0, 0) at hzero
  have hsmul : fkRectInsertedEdgeCharge R e w •
      fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) =
        (0, 0) := hdecomp'.symm.trans hzero
  apply hfund
  apply Prod.ext
  · have hx := congrArg Prod.fst hsmul
    simp only [zsmul_eq_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left hcharge
  · have hy := congrArg Prod.snd hsmul
    simp only [zsmul_eq_mul] at hy
    exact (mul_eq_zero.mp hy).resolve_left hcharge

end

end StatMech.FrontierD
