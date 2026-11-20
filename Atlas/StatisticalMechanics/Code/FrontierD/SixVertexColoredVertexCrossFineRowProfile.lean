/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexColoredLoopPairing
import Code.FrontierD.SixVertexDisagreementComponentFineRowProfile









open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexColoredVertexCrossFineRowProfilePropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



theorem sixVertexHorizontalGaugeBit_coloredArrows
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex) :
    sixVertexHorizontalGaugeBit colored.arrows.horizontal v =
      !colored.color (v, .east) := by
  unfold sixVertexHorizontalGaugeBit
  have hh : colored.arrows.horizontal v =
      !colored.incoming (v, FKMedialSide.east) := rfl
  rw [hh]
  unfold FKColoredLoopPairing.incoming fkMedialCheckerColor
    fkMedialSideVertical
  generalize hp : fkMedialVertexParity v = p
  generalize hc : colored.color (v, FKMedialSide.east) = c
  cases p <;> cases c <;> rfl


theorem fkColoredVertexCrossTarget_eastColors_eq_or_swap
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (v : T.Vertex) :
    ((fkColoredVertexCrossTarget source mask hbond false).color (v, .east),
      (fkColoredVertexCrossTarget source mask hbond true).color (v, .east)) =
        ((source false).color (v, .east),
          (source true).color (v, .east)) \/
      ((fkColoredVertexCrossTarget source mask hbond false).color (v, .east),
        (fkColoredVertexCrossTarget source mask hbond true).color (v, .east)) =
          ((source true).color (v, .east),
            (source false).color (v, .east)) := by
  have hlocal := fkColoredVertexCrossTarget_localPairing
    source mask hbond v
  have heast := congrArg
    (fun pair : FKColoredLocalPairing × FKColoredLocalPairing =>
      (pair.1.east, pair.2.east)) hlocal
  change
    ((fkColoredVertexCrossTarget source mask hbond false).color (v, .east),
      (fkColoredVertexCrossTarget source mask hbond true).color (v, .east)) =
      ((fkColoredLocalPairCrossIf (mask v)
        ((source false).localPairing v,
          (source true).localPairing v)).1.east,
       (fkColoredLocalPairCrossIf (mask v)
        ((source false).localPairing v,
          (source true).localPairing v)).2.east) at heast
  cases hm : mask v
  · left
    simpa [fkColoredLocalPairCrossIf, hm,
      FKColoredLoopPairing.localPairing] using heast
  · right
    simpa [fkColoredLocalPairCrossIf, hm,
      fkColoredLocalPairReconnection,
      FKColoredLoopPairing.localPairing] using heast


theorem fkColoredVertexCrossTarget_rowZeroProfile
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    sixVertexHorizontalPairRowZeroProfile
        ((fkColoredVertexCrossTarget source mask hbond false).arrows.horizontal,
          (fkColoredVertexCrossTarget source mask hbond true).arrows.horizontal) =
      sixVertexHorizontalPairRowZeroProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexHorizontalRowZeroCount
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sixVertexHorizontalGaugeBit_coloredArrows,
    sixVertexHorizontalGaugeBit_coloredArrows,
    sixVertexHorizontalGaugeBit_coloredArrows,
    sixVertexHorizontalGaugeBit_coloredArrows]
  rcases fkColoredVertexCrossTarget_eastColors_eq_or_swap
      source mask hbond (i, j) with hsame | hswap
  · have hfirst :
        (fkColoredVertexCrossTarget source mask hbond false).color
            ((i, j), .east) = (source false).color ((i, j), .east) := by
        simpa using congrArg Prod.fst hsame
    have hsecond :
        (fkColoredVertexCrossTarget source mask hbond true).color
            ((i, j), .east) = (source true).color ((i, j), .east) := by
        simpa using congrArg Prod.snd hsame
    rw [hfirst, hsecond]
  · have hfirst :
        (fkColoredVertexCrossTarget source mask hbond false).color
            ((i, j), .east) = (source true).color ((i, j), .east) := by
        simpa using congrArg Prod.fst hswap
    have hsecond :
        (fkColoredVertexCrossTarget source mask hbond true).color
            ((i, j), .east) = (source false).color ((i, j), .east) := by
        simpa using congrArg Prod.snd hswap
    rw [hfirst, hsecond]
    omega


theorem fkColoredVertexCrossTarget_rowNontransitionProfile
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    sixVertexHorizontalPairRowNontransitionProfile
        ((fkColoredVertexCrossTarget source mask hbond false).arrows.horizontal,
          (fkColoredVertexCrossTarget source mask hbond true).arrows.horizontal) =
      sixVertexHorizontalPairRowNontransitionProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) := by
  classical
  funext j
  unfold sixVertexHorizontalPairRowNontransitionProfile
  rw [sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  let target := fkColoredVertexCrossTarget source mask hbond
  calc
    (if (target false).arrows.IsCType (i, j) then 1 else 0) +
          (if (target true).arrows.IsCType (i, j) then 1 else 0) =
        fkColoredLocalPairCTypeCount
          ((target false).localPairing (i, j),
            (target true).localPairing (i, j)) :=
      (FKColoredLoopPairingPair.localCTypeCount target (i, j)).symm
    _ = fkColoredLocalPairCTypeCount
          (fkColoredLocalPairCrossIf (mask (i, j))
            ((source false).localPairing (i, j),
              (source true).localPairing (i, j))) := by
      rw [fkColoredVertexCrossTarget_localPairing]
    _ = fkColoredLocalPairCTypeCount
          ((source false).localPairing (i, j),
            (source true).localPairing (i, j)) := by
      cases hm : mask (i, j)
      · rfl
      · exact fkColoredLocalPairReconnection_cTypeCount _
    _ = (if (source false).arrows.IsCType (i, j) then 1 else 0) +
          (if (source true).arrows.IsCType (i, j) then 1 else 0) :=
      FKColoredLoopPairingPair.localCTypeCount source (i, j)



theorem fkColoredVertexCrossTarget_boundedFineRowProfile
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((fkColoredVertexCrossTarget source mask hbond false).arrows.horizontal,
          (fkColoredVertexCrossTarget source mask hbond true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) := by
  apply sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
  funext j
  apply Prod.ext
  · exact congrFun
      (fkColoredVertexCrossTarget_rowNontransitionProfile source mask hbond) j
  · exact congrFun
      (fkColoredVertexCrossTarget_rowZeroProfile source mask hbond) j

end

end StatMech.FrontierD
