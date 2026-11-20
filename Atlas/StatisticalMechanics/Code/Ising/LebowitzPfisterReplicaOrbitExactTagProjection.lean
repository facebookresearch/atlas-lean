/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitExactTagRecovery

open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj := Classical.decRel _

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_origin
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).1.2.1.1 =
        lpReplicaTaggedOriginProfile G sites m tag false := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_currentRow0
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).1.2.2.1.1 =
        lpReplicaTaggedRowCurrentSubset G sites m tag false false := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_currentRow1
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    let Sb0 := lpReplicaReflectCopies G sites
      (lpReplicaTaggedRowProfile G sites m tag true)
      (lpReplicaTaggedRowCurrentSubset G sites m tag true false)
    let hb := lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).1.2.2.2.1 =
      cast (congrArg
        (fun p => Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) p)) hb) Sb0 := by
  rfl

set_option maxHeartbeats 400000 in



theorem lpReplicaOrientedFourColorTag_ofRowGate
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    lpReplicaOrientedFourColorTag G sites A
      (B.map lpReplicaCurrentReflect.toEmbedding) q
      (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomOfRowGate
          G sites m q tag A B hm hgate L)) = tag := by
  funext c
  unfold lpReplicaOrientedFourColorTag
  dsimp only [lpReplicaDecoratedOrbitAtomEquivOrientedFourColor]
  simpa only [lpReplicaDecoratedOrbitAtomOfRowGate_profile,
    lpReplicaDecoratedOrbitAtomOfRowGate_origin,
    lpReplicaDecoratedOrbitAtomOfRowGate_row0,
    lpReplicaDecoratedOrbitAtomOfRowGate_currentRow0,
    lpReplicaDecoratedOrbitAtomOfRowGate_currentRow1] using
      congrFun (lpReplicaOrbitCollisionSplitTag_of_tag G sites m tag) c



theorem lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B :=
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    lpReplicaOrientedFourColorTag G sites ∅ B q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
          G sites ∅ B q z) =
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 := by
  rfl

end
end StatMech.Ising
