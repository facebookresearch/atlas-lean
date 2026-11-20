/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
import Code.FrontierD.FKRectConnectedInsertionCharge
import Code.FrontierD.FKRectBoundaryPotentialContradiction
import Code.FrontierD.FKRectPrimalBoundaryFiberWinding










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


noncomputable def fkRectRawPrimalCrossingDevelopedExtremeEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : R.EdgeIndex :=
  fkRectTorusMedialEdgeEquiv R
    (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side).1

@[simp] theorem fkRectRawPrimalCrossingDevelopedExtremeEdge_false
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X false =
      (true, fkRectRawPrimalCrossingBottomVertex R omega X) := by
  by_cases hbottom : Even
      (fkRectRawPrimalCrossingBottomVertex R omega X).2.val <;>
    simp [fkRectRawPrimalCrossingDevelopedExtremeEdge,
      fkRectRawPrimalCrossingDevelopedExtremeDart,
      fkRectMedialDartAtPrimalVertex, fkMedialWestDart,
      fkMedialEastDart, hbottom]

@[simp] theorem fkRectRawPrimalCrossingDevelopedExtremeEdge_true
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X true =
      (true,
        ((fkRectRawPrimalCrossingTopVertex R omega X).1,
          finitePeriodicSucc R.height_pos
            (fkRectRawPrimalCrossingTopVertex R omega X).2)) := by
  by_cases htop : Even
      (finitePeriodicSucc R.height_pos
        (fkRectRawPrimalCrossingTopVertex R omega X).2).val <;>
    simp [fkRectRawPrimalCrossingDevelopedExtremeEdge,
      fkRectRawPrimalCrossingDevelopedExtremeDart,
      fkRectMedialDartAbovePrimalVertex, fkMedialWestDart,
      fkMedialEastDart, htop]



theorem fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side =
        fkMedialWestDart (fkRectMedialVertexOfEdge R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side)) ∨
      fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side =
        fkMedialEastDart (fkRectMedialVertexOfEdge R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side)) := by
  cases side
  · by_cases hbottom : Even
        (fkRectRawPrimalCrossingBottomVertex R omega X).2.val
    · left
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAtPrimalVertex, hbottom]
    · right
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAtPrimalVertex, hbottom]
  · by_cases htop : Even
        (finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2).val
    · right
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAbovePrimalVertex, htop]
    · left
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAbovePrimalVertex, htop]



theorem fkRectRawPrimalCrossingDevelopedExtremeWest_checkerColor
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side =
      fkMedialWestDart (fkRectMedialVertexOfEdge R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))) :
    fkMedialCheckerColor
        (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) =
      !side := by
  cases side
  · by_cases hbottom : Even
        (fkRectRawPrimalCrossingBottomVertex R omega X).2.val
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAtPrimalVertex, fkMedialWestDart,
        fkMedialCheckerColor, fkMedialVertexParity,
        fkMedialSideVertical, hbottom, Bool.toNat]
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAtPrimalVertex, fkMedialWestDart,
        fkMedialEastDart, hbottom] at hd
  · by_cases htop : Even
        (finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2).val
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAbovePrimalVertex, fkMedialWestDart,
        fkMedialEastDart, htop] at hd
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAbovePrimalVertex, fkMedialWestDart,
        fkMedialCheckerColor, fkMedialVertexParity,
        fkMedialSideVertical, htop, Bool.toNat]



theorem fkRectRawPrimalCrossingDevelopedExtremeEast_checkerColor
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side =
      fkMedialEastDart (fkRectMedialVertexOfEdge R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))) :
    fkMedialCheckerColor
        (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) =
      side := by
  cases side
  · by_cases hbottom : Even
        (fkRectRawPrimalCrossingBottomVertex R omega X).2.val
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAtPrimalVertex, fkMedialWestDart,
        fkMedialEastDart, hbottom] at hd
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAtPrimalVertex, fkMedialEastDart,
        fkMedialCheckerColor, fkMedialVertexParity,
        fkMedialSideVertical, hbottom, Bool.toNat]
  · by_cases htop : Even
        (finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2).val
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAbovePrimalVertex, fkMedialEastDart,
        fkMedialCheckerColor, fkMedialVertexParity,
        fkMedialSideVertical, htop, Bool.toNat]
    · simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectRawPrimalCrossingDevelopedExtremeEdge,
        fkRectMedialDartAbovePrimalVertex, fkMedialWestDart,
        fkMedialEastDart, htop] at hd




theorem fkRectRawPrimalCrossingDevelopedExtremeFundamental_vertical_ne_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (C : FKRectZeroTurnCutRemainderComponent R
      (fkRectConfigurationOfEdges R F))
    (X : FKRectRawPrimalHorizontalCrossingComponent R
      (fkRectConfigurationOfEdges R F))
    (side : Bool)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X side))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X side))) :
    (fkRectWalkWinding R
      (fkRectInsertedFundamentalWalk R F
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R
          (fkRectConfigurationOfEdges R F) X side) r)).2 ≠ 0 := by
  cases side
  · let x := fkRectRawPrimalCrossingBottomVertex R
      (fkRectConfigurationOfEdges R F) X
    let y : R.Vertex :=
      (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
    by_cases heven : Even x.2.val
    · have hwest : fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X false) = x := by
        simp [x, fkRectMedialWestPrimal, heven]
      have heast : fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X false) = y := by
        simp [x, y, fkRectMedialEastPrimal, heven]
      let r' : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk x y :=
        r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos
          R (fkRectConfigurationOfEdges R F) C X r'
      rw [fkRectWalkWinding_copy] at hclose
      rw [fkRectInsertedFundamentalWalk_winding]
      simpa [x, y, fkRectMedialWestPrimal,
        fkRectMedialEastPrimal, heven] using hclose.ne'
    · have hwest : fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X false) = y := by
        simp [x, y, fkRectMedialWestPrimal, heven]
      have heast : fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X false) = x := by
        simp [x, fkRectMedialEastPrimal, heven]
      let r' : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk y x :=
        r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos
          R (fkRectConfigurationOfEdges R F) C X r'.reverse
      rw [fkRectWalkWinding_reverse,
        fkRectWalkWinding_copy,
        fkRectVerticalSeamIncrement_swap] at hclose
      rw [fkRectInsertedFundamentalWalk_winding]
      simp [x, fkRectMedialWestPrimal,
        fkRectMedialEastPrimal, heven]
      intro hzero
      have hzero' : (fkRectWalkWinding R r).2 +
          fkRectVerticalSeamIncrement R x y = 0 := by
        simpa [x, y] using hzero
      have hnegzero :
          -(fkRectWalkWinding R r).2 +
              -fkRectVerticalSeamIncrement R x y = 0 := by
        calc
          -(fkRectWalkWinding R r).2 +
                -fkRectVerticalSeamIncrement R x y =
              -((fkRectWalkWinding R r).2 +
                fkRectVerticalSeamIncrement R x y) := by ring
          _ = 0 := by rw [hzero']; simp
      exact hclose.ne' hnegzero
  · let x := fkRectRawPrimalCrossingTopVertex R
      (fkRectConfigurationOfEdges R F) X
    let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
    by_cases heven : Even y.2.val
    · have hwest : fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X true) = y := by
        simp [x, y, fkRectMedialWestPrimal, heven]
      have heast : fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X true) = x := by
        simp [x, y, fkRectMedialEastPrimal, heven,
          svCyclicPred_finitePeriodicSucc]
      let r' : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk y x :=
        r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingTopClosing_verticalWinding_neg
          R (fkRectConfigurationOfEdges R F) C X r'.reverse
      rw [fkRectWalkWinding_reverse,
        fkRectWalkWinding_copy,
        fkRectVerticalSeamIncrement_swap] at hclose
      rw [fkRectInsertedFundamentalWalk_winding]
      simp [x, y, fkRectMedialWestPrimal,
        fkRectMedialEastPrimal, heven,
        svCyclicPred_finitePeriodicSucc]
      intro hzero
      have hzero' : (fkRectWalkWinding R r).2 +
          fkRectVerticalSeamIncrement R x y = 0 := by
        simpa [x, y] using hzero
      have hnegzero :
          -(fkRectWalkWinding R r).2 +
              -fkRectVerticalSeamIncrement R x y = 0 := by
        calc
          -(fkRectWalkWinding R r).2 +
                -fkRectVerticalSeamIncrement R x y =
              -((fkRectWalkWinding R r).2 +
                fkRectVerticalSeamIncrement R x y) := by ring
          _ = 0 := by rw [hzero']; simp
      exact hclose.ne hnegzero
    · have hwest : fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X true) = x := by
        simp [x, y, fkRectMedialWestPrimal, heven,
          svCyclicPred_finitePeriodicSucc]
      have heast : fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X true) = y := by
        simp [x, y, fkRectMedialEastPrimal, heven]
      let r' : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk x y :=
        r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingTopClosing_verticalWinding_neg
          R (fkRectConfigurationOfEdges R F) C X r'
      rw [fkRectWalkWinding_copy] at hclose
      rw [fkRectInsertedFundamentalWalk_winding]
      simpa [x, y, fkRectMedialWestPrimal,
        fkRectMedialEastPrimal, heven,
        svCyclicPred_finitePeriodicSucc] using hclose.ne



theorem fkRectRawPrimalCrossingDevelopedExtremeWest_winding_fst_pos
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (C : FKRectZeroTurnCutRemainderComponent R
      (fkRectConfigurationOfEdges R F))
    (X : FKRectRawPrimalHorizontalCrossingComponent R
      (fkRectConfigurationOfEdges R F))
    (side : Bool)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X side))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X side)))
    (heF : fkRectRawPrimalCrossingDevelopedExtremeEdge R
      (fkRectConfigurationOfEdges R F) X side ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R
              (fkRectConfigurationOfEdges R F) X side)))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R
              (fkRectConfigurationOfEdges R F) X side))))
    (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R
        (fkRectConfigurationOfEdges R F) X side =
      fkMedialWestDart (fkRectMedialVertexOfEdge R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R
          (fkRectConfigurationOfEdges R F) X side))) :
    0 < (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R
        (fkRectConfigurationOfEdges R F)
        (fkRectRawPrimalCrossingDevelopedExtremeDart R
          (fkRectConfigurationOfEdges R F) X side))).1 := by
  let omega := fkRectConfigurationOfEdges R F
  let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side
  have hsign := fkRectConnectedInsertion_boundary_windingDet_signs
    R F e r heF hsep
  have hy :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
  cases side
  · let x := fkRectRawPrimalCrossingBottomVertex R omega X
    let y : R.Vertex :=
      (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
    by_cases heven : Even x.2.val
    · have hwest : fkRectMedialWestPrimal R e = x := by
        simp [e, omega, x, fkRectMedialWestPrimal, heven]
      have heast : fkRectMedialEastPrimal R e = y := by
        simp [e, omega, x, y, fkRectMedialEastPrimal, heven]
      let r' : (fkRectOpenGraph R omega).Walk x y := r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos
          R omega C X r'
      rw [fkRectWalkWinding_copy] at hclose
      have hfund : (0 : Int) <
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)).2 := by
        rw [fkRectInsertedFundamentalWalk_winding]
        simpa [e, omega, x, y, fkRectMedialWestPrimal,
          fkRectMedialEastPrimal, heven,
          fkRectWalkWinding_copy] using hclose
      dsimp only at hsign
      rw [if_neg (by simp [e, omega, x, fkRectClosedPairingAtEdge,
        heven])] at hsign
      change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F)
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))).2 = 0 at hy
      rw [hy] at hsign
      simp only [zero_mul, sub_zero] at hsign
      rw [hd]
      nlinarith [hsign.1, hfund]
    · exfalso
      have hd' := hd
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAtPrimalVertex, e, omega, x, heven] at hd'
      exact (by
        simpa [fkMedialEastDart, fkMedialWestDart] using hd')
  · let x := fkRectRawPrimalCrossingTopVertex R omega X
    let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
    by_cases heven : Even y.2.val
    · exfalso
      have hd' := hd
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAbovePrimalVertex, e, omega, x, y, heven] at hd'
      exact (by
        simpa [fkMedialEastDart, fkMedialWestDart] using hd')
    · have hwest : fkRectMedialWestPrimal R e = x := by
        simp [e, omega, x, y, fkRectMedialWestPrimal, heven,
          svCyclicPred_finitePeriodicSucc]
      have heast : fkRectMedialEastPrimal R e = y := by
        simp [e, omega, x, y, fkRectMedialEastPrimal, heven]
      let r' : (fkRectOpenGraph R omega).Walk x y := r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingTopClosing_verticalWinding_neg
          R omega C X r'
      rw [fkRectWalkWinding_copy] at hclose
      have hfund :
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)).2 < 0 := by
        rw [fkRectInsertedFundamentalWalk_winding]
        simpa [e, omega, x, y, fkRectMedialWestPrimal,
          fkRectMedialEastPrimal, heven,
          svCyclicPred_finitePeriodicSucc,
          fkRectWalkWinding_copy] using hclose
      dsimp only at hsign
      rw [if_pos (by simp [e, omega, x, y,
        fkRectClosedPairingAtEdge, heven])] at hsign
      change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F)
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))).2 = 0 at hy
      rw [hy] at hsign
      simp only [zero_mul, sub_zero] at hsign
      rw [hd]
      nlinarith [hsign.1, hfund]



theorem fkRectRawPrimalCrossingDevelopedExtremeEast_winding_fst_neg
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (C : FKRectZeroTurnCutRemainderComponent R
      (fkRectConfigurationOfEdges R F))
    (X : FKRectRawPrimalHorizontalCrossingComponent R
      (fkRectConfigurationOfEdges R F))
    (side : Bool)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X side))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X side)))
    (heF : fkRectRawPrimalCrossingDevelopedExtremeEdge R
      (fkRectConfigurationOfEdges R F) X side ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R
              (fkRectConfigurationOfEdges R F) X side)))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R
              (fkRectConfigurationOfEdges R F) X side))))
    (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R
        (fkRectConfigurationOfEdges R F) X side =
      fkMedialEastDart (fkRectMedialVertexOfEdge R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R
          (fkRectConfigurationOfEdges R F) X side))) :
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R
        (fkRectConfigurationOfEdges R F)
        (fkRectRawPrimalCrossingDevelopedExtremeDart R
          (fkRectConfigurationOfEdges R F) X side))).1 < 0 := by
  let omega := fkRectConfigurationOfEdges R F
  let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side
  have hsign := fkRectConnectedInsertion_boundary_windingDet_signs
    R F e r heF hsep
  have hy :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C (fkMedialEastDart (fkRectMedialVertexOfEdge R e))
  cases side
  · let x := fkRectRawPrimalCrossingBottomVertex R omega X
    let y : R.Vertex :=
      (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
    by_cases heven : Even x.2.val
    · exfalso
      have hd' := hd
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAtPrimalVertex, omega, x, heven] at hd'
      exact (by
        simpa [fkMedialEastDart, fkMedialWestDart] using hd'.symm)
    · have hwest : fkRectMedialWestPrimal R e = y := by
        simp [e, omega, x, y, fkRectMedialWestPrimal, heven]
      have heast : fkRectMedialEastPrimal R e = x := by
        simp [e, omega, x, fkRectMedialEastPrimal, heven]
      let r' : (fkRectOpenGraph R omega).Walk y x := r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos
          R omega C X r'.reverse
      rw [fkRectWalkWinding_reverse, fkRectWalkWinding_copy,
        fkRectVerticalSeamIncrement_swap] at hclose
      change 0 < -(fkRectWalkWinding R r).2 +
        -fkRectVerticalSeamIncrement R x y at hclose
      have hfund :
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)).2 < 0 := by
        rw [fkRectInsertedFundamentalWalk_winding]
        simp [e, omega, x, y, fkRectMedialWestPrimal,
          fkRectMedialEastPrimal, heven]
        change (fkRectWalkWinding R r).2 +
          fkRectVerticalSeamIncrement R x y < 0
        nlinarith
      dsimp only at hsign
      have hpair : fkRectClosedPairingAtEdge e = true := by
        simp [e, omega, x, fkRectClosedPairingAtEdge, heven]
      simp only [if_pos hpair] at hsign
      change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F)
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))).2 = 0 at hy
      rw [hy] at hsign
      simp only [zero_mul, sub_zero] at hsign
      rw [hd]
      nlinarith [hsign.2, hfund]
  · let x := fkRectRawPrimalCrossingTopVertex R omega X
    let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
    by_cases heven : Even y.2.val
    · have hwest : fkRectMedialWestPrimal R e = y := by
        simp [e, omega, x, y, fkRectMedialWestPrimal, heven]
      have heast : fkRectMedialEastPrimal R e = x := by
        simp [e, omega, x, y, fkRectMedialEastPrimal, heven,
          svCyclicPred_finitePeriodicSucc]
      let r' : (fkRectOpenGraph R omega).Walk y x := r.copy hwest heast
      have hclose :=
        fkRectRawPrimalCrossingTopClosing_verticalWinding_neg
          R omega C X r'.reverse
      rw [fkRectWalkWinding_reverse, fkRectWalkWinding_copy,
        fkRectVerticalSeamIncrement_swap] at hclose
      change -(fkRectWalkWinding R r).2 +
        -fkRectVerticalSeamIncrement R x y < 0 at hclose
      have hfund : (0 : Int) <
          (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)).2 := by
        rw [fkRectInsertedFundamentalWalk_winding]
        simp [e, omega, x, y, fkRectMedialWestPrimal,
          fkRectMedialEastPrimal, heven,
          svCyclicPred_finitePeriodicSucc]
        change 0 < (fkRectWalkWinding R r).2 +
          fkRectVerticalSeamIncrement R x y
        nlinarith
      dsimp only at hsign
      have hpair : ¬ fkRectClosedPairingAtEdge e = true := by
        simp [e, omega, x, y, fkRectClosedPairingAtEdge, heven]
      simp only [if_neg hpair] at hsign
      change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F)
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))).2 = 0 at hy
      rw [hy] at hsign
      simp only [zero_mul, sub_zero] at hsign
      rw [hd]
      nlinarith [hsign.2, hfund]
    · exfalso
      have hd' := hd
      simp [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAbovePrimalVertex, omega, x, y, heven] at hd'
      exact (by
        simpa [fkMedialEastDart, fkMedialWestDart] using hd'.symm)



theorem fkRectRawPrimalCrossingDevelopedExtremeWest_reachable_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hwe : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))
      (fkRectMedialDartPrimalLabel R
        (fkRectZeroTurnRemainderBlackDart R omega C).1) := by
  have hwestd : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))
      (fkRectMedialDartPrimalLabel R
        (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side)) := by
    rcases fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east
      R omega X side with hd | hd
    · rw [hd, fkRectMedialDartPrimalLabel_west_vertexOfEdge]
    · rw [hd, fkRectMedialDartPrimalLabel_east_vertexOfEdge]
      exact hwe
  have hextreme :
      (fkRectOpenGraph R omega).connectedComponentMk
          (fkRectMedialDartPrimalLabel R
            (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side)) =
        fkRectZeroTurnRemainderPrimalComponent R omega C := by
    unfold fkRectZeroTurnRemainderPrimalComponent
    rw [← fkRectMedialComponentToPrimalComponent_mk,
      fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent]
    exact fkRectZeroTurnPrimalTouchedCrossing_matches R omega C X hX
  have hblack :
      (fkRectOpenGraph R omega).connectedComponentMk
          (fkRectMedialDartPrimalLabel R
            (fkRectZeroTurnRemainderBlackDart R omega C).1) =
        fkRectZeroTurnRemainderPrimalComponent R omega C := by
    unfold fkRectZeroTurnRemainderPrimalComponent
    rw [← fkRectMedialComponentToPrimalComponent_mk,
      fkRectZeroTurnRemainderBlackDart_component]
  have hcomponents :
      (fkRectOpenGraph R omega).connectedComponentMk
          (fkRectMedialDartPrimalLabel R
            (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side)) =
        (fkRectOpenGraph R omega).connectedComponentMk
          (fkRectMedialDartPrimalLabel R
            (fkRectZeroTurnRemainderBlackDart R omega C).1) := by
    exact hextreme.trans hblack.symm
  exact hwestd.trans (SimpleGraph.ConnectedComponent.exact hcomponents)







set_option maxHeartbeats 2000000 in

theorem fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_edges
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (C : FKRectZeroTurnCutRemainderComponent R
      (fkRectConfigurationOfEdges R F))
    (X : FKRectRawPrimalHorizontalCrossingComponent R
      (fkRectConfigurationOfEdges R F))
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R
      (fkRectConfigurationOfEdges R F) C) :
    ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
        (fkMedialWestDart (fkRectMedialVertexOfEdge R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C))))
        (fkMedialEastDart (fkRectMedialVertexOfEdge R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C)))) := by
  let omega := fkRectConfigurationOfEdges R F
  let side := fkRectZeroTurnRemainderSide R omega C
  let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side
  intro hmedial
  have hprimal := fkRectMedial_reachable_primalLabel_reachable
    R omega hmedial
  simp only [fkRectMedialDartPrimalLabel_west_vertexOfEdge,
    fkRectMedialDartPrimalLabel_east_vertexOfEdge] at hprimal
  obtain ⟨r⟩ := hprimal
  have heclosed :=
    fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed
      R omega C X side
  have heF : e ∉ F := by
    intro he
    have hopen : omega e = true := by
      exact (fkRectConfigurationOfEdges_apply R F e).2 he
    change omega e = false at heclosed
    exact Bool.noConfusion (hopen.symm.trans heclosed)
  have hwestblack :=
    fkRectRawPrimalCrossingDevelopedExtremeWest_reachable_remainder
      R omega C X side hX ⟨r⟩
  obtain ⟨s⟩ := hwestblack
  let b := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  let q := (s.append b).append s.reverse
  have hqwind : fkRectWalkWinding R q = fkRectWalkWinding R b := by
    exact fkRectWalkWinding_conjugate R s b
  have hb1 : (fkRectWalkWinding R b).1 ≠ 0 :=
    fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  have hb2 : (fkRectWalkWinding R b).2 = 0 :=
    fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero R omega C
  have hfund2 :
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)).2 ≠ 0 :=
    fkRectRawPrimalCrossingDevelopedExtremeFundamental_vertical_ne_zero
      R F C X side r
  have hind : FKRectWindingIndependent
      (fkRectWalkWinding R q)
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) := by
    unfold FKRectWindingIndependent
    rw [hqwind, hb2]
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero hb1 hfund2
  have hold : ¬ FKRectHasNet R omega :=
    not_fkRectHasNet_of_zeroTurnRemainder R omega C
  have hsurface := fkRectConnectedInsertionSurfaceBridge_unconditional
    R F e r heF hold
  exact (hsurface.mpr ⟨q, hind⟩) hmedial


theorem fkRectRawPrimalCrossingDevelopedExtreme_not_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
    ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable
        (fkMedialWestDart (fkRectMedialVertexOfEdge R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C))))
        (fkMedialEastDart (fkRectMedialVertexOfEdge R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C)))) := by
  generalize hF : fkRectOpenEdges R omega = F
  have hconfig : fkRectConfigurationOfEdges R F = omega := by
    rw [← hF]
    exact fkRectConfigurationOfEdges_openEdges R omega
  clear hF
  cases hconfig
  exact fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_edges
    R F C X hX




theorem
    fkRectZeroTurnRemainderOrientedDart_avoids_developedExtreme_localSides
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hendpoint : ¬ (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C))))
    (hcomponent :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) ≠ C.1) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
      (fkRectZeroTurnRemainderSide R omega C)
    let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
      (fkRectZeroTurnRemainderSide R omega C)
    let dB := fkRectZeroTurnRemainderOrientedDart R omega C
      (fkMedialCheckerColor dA)
    ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠
          fkMedialWestDart (fkRectMedialVertexOfEdge R e) ∧
        (fkMedialBoundaryStep pairing)^[k] dB ≠
          fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let side := fkRectZeroTurnRemainderSide R omega C
  let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side
  let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side
  let dB := fkRectZeroTurnRemainderOrientedDart R omega C
    (fkMedialCheckerColor dA)
  have hBcomponent :
      (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk dB =
        C.1 :=
    fkRectZeroTurnRemainderOrientedDart_component R omega C
      (fkMedialCheckerColor dA)
  have hclusterA :=
    fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component
      R omega C X hX
  have hclusterB :
      fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk dB) =
        fkRectZeroTurnRemainderPrimalComponent R omega C := by
    rw [hBcomponent]
    rfl
  have hprimalAB : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R dA)
      (fkRectMedialDartPrimalLabel R dB) := by
    apply SimpleGraph.ConnectedComponent.exact
    change (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R dA) =
      (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R dB)
    exact hclusterA.trans hclusterB.symm
  rcases fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east
      R omega X side with hdA | hdA
  · intro k
    constructor
    · intro hk
      apply hcomponent
      have hreach := fkMedialBoundaryStep_iterate_reachable pairing dB k
      rw [hk, ← hdA] at hreach
      exact (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hBcomponent
    · intro hk
      have hreach := fkMedialBoundaryStep_iterate_reachable pairing dB k
      rw [hk] at hreach
      have hp := fkRectMedial_reachable_primalLabel_reachable
        R omega hreach
      apply hendpoint
      simpa [e, dA, hdA,
        fkRectMedialDartPrimalLabel_west_vertexOfEdge,
        fkRectMedialDartPrimalLabel_east_vertexOfEdge] using
          hprimalAB.trans hp
  · intro k
    constructor
    · intro hk
      have hreach := fkMedialBoundaryStep_iterate_reachable pairing dB k
      rw [hk] at hreach
      have hp := fkRectMedial_reachable_primalLabel_reachable
        R omega hreach
      apply hendpoint
      simpa [e, dA, hdA,
        fkRectMedialDartPrimalLabel_west_vertexOfEdge,
        fkRectMedialDartPrimalLabel_east_vertexOfEdge] using
          (hprimalAB.trans hp).symm
    · intro hk
      apply hcomponent
      have hreach := fkMedialBoundaryStep_iterate_reachable pairing dB k
      rw [hk, ← hdA] at hreach
      exact (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hBcomponent



theorem
    fkRectZeroTurnRemainderOrientedDart_developedExtreme_interaction_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (C : FKRectZeroTurnCutRemainderComponent R
      (fkRectConfigurationOfEdges R F))
    (X : FKRectRawPrimalHorizontalCrossingComponent R
      (fkRectConfigurationOfEdges R F))
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R
      (fkRectConfigurationOfEdges R F) C)
    (hendpoint : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C)))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C))))
    (hcomponent :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C)) ≠ C.1) :
    let omega := fkRectConfigurationOfEdges R F
    let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
      (fkRectZeroTurnRemainderSide R omega C)
    let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
      (fkRectZeroTurnRemainderSide R omega C)
    let dB := fkRectZeroTurnRemainderOrientedDart R omega C
      (fkMedialCheckerColor dA)
    let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let side := fkRectZeroTurnRemainderSide R omega C
  let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side
  let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side
  let dB := fkRectZeroTurnRemainderOrientedDart R omega C
    (fkMedialCheckerColor dA)
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have heclosed :=
    fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed
      R omega C X side
  have heF : e ∉ F := by
    intro he
    have hopen : omega e = true :=
      (fkRectConfigurationOfEdges_apply R F e).2 he
    change omega e = false at heclosed
    exact Bool.noConfusion (hopen.symm.trans heclosed)
  have havoid :=
    fkRectZeroTurnRemainderOrientedDart_avoids_developedExtreme_localSides
      R omega C X hX hendpoint hcomponent
  dsimp only at havoid
  have hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) := by
    have hB := fkRectZeroTurnRemainderOrientedDart_checkerColor
      R omega C (fkMedialCheckerColor dA)
    change fkMedialCheckerColor dB = fkMedialCheckerColor dA at hB
    rw [hB]
    dsimp only [dA, e]
    rcases fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east
        R omega X side with hdA | hdA
    · rw [hdA]
    · rw [hdA]
      simp [fkMedialCheckerColor, fkMedialWestDart,
        fkMedialEastDart, fkMedialSideVertical]
  have hzero :=
    fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_eq_zero_of_avoid_west_east
      R F e heF dB wB hcolor
        (fun k => (havoid k).1) (fun k => (havoid k).2)
  change fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) = 0
  simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
    fkRectCanonicalRefinedBoundaryOrbitDarts,
    fkRectSquareCoverDartList, pairing, n, L, wB, omega,
    fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using hzero

set_option maxHeartbeats 2000000 in



theorem fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (C : FKRectZeroTurnCutRemainderComponent R
      (fkRectConfigurationOfEdges R F))
    (X : FKRectRawPrimalHorizontalCrossingComponent R
      (fkRectConfigurationOfEdges R F))
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R
      (fkRectConfigurationOfEdges R F) C)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C)))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R
            (fkRectConfigurationOfEdges R F) X
            (fkRectZeroTurnRemainderSide R
              (fkRectConfigurationOfEdges R F) C)))) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).connectedComponentMk
        (fkRectRawPrimalCrossingDevelopedExtremeDart R
          (fkRectConfigurationOfEdges R F) X
          (fkRectZeroTurnRemainderSide R
            (fkRectConfigurationOfEdges R F) C)) = C.1 := by
  let omega := fkRectConfigurationOfEdges R F
  let side := fkRectZeroTurnRemainderSide R omega C
  let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side
  let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side
  let color := fkMedialCheckerColor dA
  let dB := fkRectZeroTurnRemainderOrientedDart R omega C color
  have hsep := fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_edges
    R F C X hX
  have heclosed :=
    fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed
      R omega C X side
  have heF : e ∉ F := by
    intro he
    have hopen : omega e = true :=
      (fkRectConfigurationOfEdges_apply R F e).2 he
    change omega e = false at heclosed
    exact Bool.noConfusion (hopen.symm.trans heclosed)
  have hBcomponent :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          dB = C.1 := by
    exact fkRectZeroTurnRemainderOrientedDart_component R omega C color
  by_contra hcomponent
  have hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable dA dB := by
    intro hreach
    apply hcomponent
    exact (SimpleGraph.ConnectedComponent.sound hreach).trans hBcomponent
  have hcolorB : fkMedialCheckerColor dB = fkMedialCheckerColor dA := by
    exact fkRectZeroTurnRemainderOrientedDart_checkerColor R omega C color
  have hyB :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C dB
  rcases fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east
      R omega X side with hd | hd
  · have hxA :=
      fkRectRawPrimalCrossingDevelopedExtremeWest_winding_fst_pos
        R F C X side r heF hsep hd
    rw [hd] at hxA
    have hsideColor : side = !color := by
      dsimp only [color, dA]
      rw [fkRectRawPrimalCrossingDevelopedExtremeWest_checkerColor
        R omega X side hd]
      cases side <;> rfl
    have hxB :=
      (fkRectZeroTurnRemainderOrientedDart_winding_fst_pos_iff
        R omega C color).2 hsideColor
    have hcolorW : fkMedialCheckerColor dB =
        fkMedialCheckerColor
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) := by
      exact hcolorB.trans (congrArg fkMedialCheckerColor hd)
    have hBsepW : ¬ (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB := by
      intro hreach
      apply hBsep
      change (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) dB
      rw [hd]
      exact hreach
    have hyA :=
      fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
        R omega C (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
    apply fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction
      R F e r heF hsep dB hcolorW hBsepW
    · exact mul_pos hxA hxB
    · exact hyA
    · exact hyB
  · have hxA :=
      fkRectRawPrimalCrossingDevelopedExtremeEast_winding_fst_neg
        R F C X side r heF hsep hd
    rw [hd] at hxA
    have hsideColor : side = color := by
      dsimp only [color, dA]
      exact (fkRectRawPrimalCrossingDevelopedExtremeEast_checkerColor
        R omega X side hd).symm
    have hxB :=
      (fkRectZeroTurnRemainderOrientedDart_winding_fst_neg_iff
        R omega C color).2 hsideColor
    have hcolorE : fkMedialCheckerColor dB =
        fkMedialCheckerColor
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
      exact hcolorB.trans (congrArg fkMedialCheckerColor hd)
    have hBsepE : ¬ (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB := by
      intro hreach
      apply hBsep
      change (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) dB
      rw [hd]
      exact hreach
    have hyA :=
      fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
        R omega C (fkMedialEastDart (fkRectMedialVertexOfEdge R e))
    apply
      fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction_east
        R F e r heF hsep dB hcolorE hBsepE
    · exact mul_pos_of_neg_of_neg hxA hxB
    · exact hyA
    · exact hyB



theorem fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hreach : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
          (fkRectZeroTurnRemainderSide R omega C)) = C.1 := by
  generalize hF : fkRectOpenEdges R omega = F
  have hconfig : fkRectConfigurationOfEdges R F = omega := by
    rw [← hF]
    exact fkRectConfigurationOfEdges_openEdges R omega
  clear hF
  cases hconfig
  obtain ⟨r⟩ := hreach
  exact
    fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointWalk
      R F C X hX r






theorem
    fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_of_endpointReachable
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D)
    (hreachC : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C))))
    (hreachD : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega D)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega D))))
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    C = D := by
  have hC :=
    fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable
      R omega C X hXC hreachC
  have hD :=
    fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable
      R omega D X hXD hreachD
  apply Subtype.ext
  calc
    C.1 = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) := hC.symm
    _ = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega D)) := by rw [hside]
    _ = D.1 := hD




def FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega),
    X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
      ¬ (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C)))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C))) →
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) = C.1






def FKRectPrimalBoundaryFiberSameSignUnique
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
    ¬ FKRectHasNet R omega →
    ∀ d e : FKMedialDart R.medialTorus,
      fkMedialCheckerColor d = fkMedialCheckerColor e →
      fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              d) =
        fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              e) →
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 = 0 →
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).2 = 0 →
      0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).1 →
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d =
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk e

set_option maxHeartbeats 800000 in





theorem fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (hcard : ¬ FKRectHasNet R omega → ∀ x : R.Vertex,
      (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2) :
    FKRectPrimalBoundaryFiberSameSignUnique R omega := by
  classical
  intro hnoNet d e hcolor hfiber _hdVertical _heVertical hsign
  let pairing := fkRectConfigurationToMedialPairing R omega
  have blackCase (d0 e0 : FKMedialDart R.medialTorus)
      (bd be : FKMedialBlackDart R.medialTorus)
      (hbd : bd.1 = d0) (hbe : be.1 = e0)
      (hfiber0 : fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d0) =
        fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e0))
      (hsign0 : 0 < (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d0)).1 *
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega e0)).1) :
      (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d0 =
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e0 := by
    let x := fkRectMedialDartPrimalLabel R d0
    have hreach : (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R e0) := by
      apply SimpleGraph.ConnectedComponent.exact
      simpa [pairing] using hfiber0
    let C : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bd
    let D : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ be
    have hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C := by
      rw [show C = Quot.mk _ bd from rfl,
        fkRectBlackBoundaryCycleInPrimalCluster_mk]
      simpa [x, hbd] using
        (SimpleGraph.Reachable.refl x :
          (fkRectOpenGraph R omega).Reachable x x)
    have hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D := by
      rw [show D = Quot.mk _ be from rfl,
        fkRectBlackBoundaryCycleInPrimalCluster_mk]
      simpa [hbe] using hreach
    let md := permOrbitVisitCount (fkMedialBoundaryStep pairing) bd.1 bd.1
    let me := permOrbitVisitCount (fkMedialBoundaryStep pairing) be.1 be.1
    have hmd : 0 < md := permOrbitVisitCount_self_pos _ _
    have hme : 0 < me := permOrbitVisitCount_self_pos _ _
    have hdscale := congrArg Prod.fst
      (fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
        R omega bd)
    have hescale := congrArg Prod.fst
      (fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
        R omega be)
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass] at hdscale hescale
    simp only [Prod.smul_fst, nsmul_eq_mul] at hdscale hescale
    have hsign' := hsign0
    rw [← hbd, ← hbe, hdscale, hescale] at hsign'
    have hmdInt : (0 : Int) < md := by exact_mod_cast hmd
    have hmeInt : (0 : Int) < me := by exact_mod_cast hme
    have hfactor : 0 < ((md : Int) * (me : Int)) *
        ((fkRectBlackBoundaryCycleClassWinding R pairing bd).1 *
          (fkRectBlackBoundaryCycleClassWinding R pairing be).1) := by
      rw [show ((md : Int) * (me : Int)) *
          ((fkRectBlackBoundaryCycleClassWinding R pairing bd).1 *
            (fkRectBlackBoundaryCycleClassWinding R pairing be).1) =
        ((md : Int) *
            (fkRectBlackBoundaryCycleClassWinding R pairing bd).1) *
          ((me : Int) *
            (fkRectBlackBoundaryCycleClassWinding R pairing be).1) by ring]
      simpa [md, me, pairing] using hsign'
    have hcycleSign : 0 <
        (fkRectBlackBoundaryCycleClassWinding R pairing bd).1 *
          (fkRectBlackBoundaryCycleClassWinding R pairing be).1 := by
      rcases (mul_pos_iff.mp hfactor) with hpos | hneg
      · exact hpos.2
      · exact absurd hneg.1 (not_lt_of_ge (mul_nonneg hmdInt.le hmeInt.le))
    have hCD : C = D := by
      apply fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
        R omega x (hcard hnoNet x) hC hD
      simpa [C, D, pairing] using hcycleSign
    have hsame : (fkMedialBlackBoundaryPerm pairing).SameCycle bd be := by
      exact Quotient.exact hCD
    apply SimpleGraph.ConnectedComponent.sound
    simpa [hbd, hbe] using
      (fkMedial_blackBoundary_sameCycle_iff_reachable pairing bd be).mp hsame
  cases hdcolor : fkMedialCheckerColor d
  · have hecolor : fkMedialCheckerColor e = false := by
      rw [← hcolor, hdcolor]
    exact blackCase d e ⟨d, hdcolor⟩ ⟨e, hecolor⟩ rfl rfl
      hfiber hsign
  · have hecolor : fkMedialCheckerColor e = true := by
      rw [← hcolor, hdcolor]
    let d' := fkMedialLocalMate pairing d
    let e' := fkMedialLocalMate pairing e
    have hd'black : fkMedialCheckerColor d' = false := by
      simp [d', fkMedialCheckerColor_localMate_eq_not, hdcolor]
    have he'black : fkMedialCheckerColor e' = false := by
      simp [e', fkMedialCheckerColor_localMate_eq_not, hecolor]
    have hdComponent :
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d' =
          (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_reachable_localMate pairing d).symm
    have heComponent :
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e' =
          (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_reachable_localMate pairing e).symm
    have hfiber' :
        fkRectMedialComponentToPrimalComponent R omega
            ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d') =
          fkRectMedialComponentToPrimalComponent R omega
            ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e') := by
      rw [hdComponent, heComponent]
      exact hfiber
    have hsign' : 0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d')).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega e')).1 := by
      rw [show d' = fkMedialLocalMate pairing d from rfl,
        show e' = fkMedialLocalMate pairing e from rfl,
        fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate,
        fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate]
      simpa using hsign
    have hde' := blackCase d' e' ⟨d', hd'black⟩ ⟨e', he'black⟩
      rfl rfl hfiber' hsign'
    exact hdComponent.symm.trans (hde'.trans heComponent)



def FKRectPrimalDevelopedExtremeSameSign
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
    ∀ (C : FKRectZeroTurnCutRemainderComponent R omega)
      (X : FKRectRawPrimalHorizontalCrossingComponent R omega),
      X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
      ¬ (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C)))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C))) →
      let d := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
        (fkRectZeroTurnRemainderSide R omega C)
      let e := fkRectZeroTurnRemainderOrientedDart R omega C
        (fkMedialCheckerColor d)
      0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).1




structure FKRectPrimalRankOneRegularNeighborhood
    (R : FKRectTorus) (omega : R.Configuration) : Prop where
  sameSign_unique : FKRectPrimalBoundaryFiberSameSignUnique R omega
  developedExtreme_sameSign : FKRectPrimalDevelopedExtremeSameSign R omega



def FKRectPrimalRankOneRegularNeighborhood.ofParts
    (R : FKRectTorus) (omega : R.Configuration)
    (hunique : FKRectPrimalBoundaryFiberSameSignUnique R omega)
    (hextreme : FKRectPrimalDevelopedExtremeSameSign R omega) :
    FKRectPrimalRankOneRegularNeighborhood R omega where
  sameSign_unique := hunique
  developedExtreme_sameSign := hextreme



theorem fkRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence_of_regularNeighborhood
    (R : FKRectTorus) (omega : R.Configuration)
    (hregular : FKRectPrimalRankOneRegularNeighborhood R omega) :
    FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega := by
  intro C X hX hdisc
  let d := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
    (fkRectZeroTurnRemainderSide R omega C)
  let e := fkRectZeroTurnRemainderOrientedDart R omega C
    (fkMedialCheckerColor d)
  have hnoNet : ¬ FKRectHasNet R omega :=
    not_fkRectHasNet_of_zeroTurnRemainder R omega C
  have heComponent : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk e =
      C.1 := by
    exact fkRectZeroTurnRemainderOrientedDart_component R omega C _
  have hfiber :
      fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              d) =
        fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              e) := by
    calc
      fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              d) = fkRectZeroTurnRemainderPrimalComponent R omega C := by
        exact fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component
          R omega C X hX
      _ = fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              e) := by
        unfold fkRectZeroTurnRemainderPrimalComponent
        rw [heComponent]
  have hcolor : fkMedialCheckerColor d = fkMedialCheckerColor e := by
    dsimp only [e]
    symm
    exact fkRectZeroTurnRemainderOrientedDart_checkerColor R omega C _
  have hdVertical : (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 = 0 :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C d
  have heVertical : (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).2 = 0 :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C e
  have hsign : 0 < (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).1 := by
    exact hregular.developedExtreme_sameSign C X hX hdisc
  calc
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) =
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            e := by
      exact hregular.sameSign_unique hnoNet d e hcolor hfiber hdVertical
        heVertical hsign
    _ = C.1 := heComponent



theorem fkRectZeroTurnPrimalDevelopedExtremeIncidence_of_disconnected
    (R : FKRectTorus) (omega : R.Configuration)
    (hdisconnected :
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega) :
    FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega := by
  intro C X hX
  by_cases hreach : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
  · exact
      fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable
        R omega C X hX hreach
  · exact hdisconnected C X hX hreach

end

end StatMech.FrontierD
