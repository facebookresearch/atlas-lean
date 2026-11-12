/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRowGate








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRouteTargetDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem lpReplicaRowGate_canonicalizeRawPartialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (rawTag : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P)) ->
      LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hraw : LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      A B rawTag) :
    LPReplicaRowGate G sites
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      A B
      (lpReplicaTransportTag G sites
        (lpReplicaPartialReflectCanonicalRelabelEquiv
          G sites q m hm L P) rawTag) :=
  lpReplicaRowGate_transportTag G sites
    (lpReplicaPartialReflectCanonicalRelabelEquiv G sites q m hm L P)
    (lpReplicaPartialReflectCanonicalRelabelEquiv_ends
      G sites q m hm L P)
    A B rawTag hraw



noncomputable def lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (rawTag : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P)) ->
      LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hraw : LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      A B rawTag) :
    LPReplicaDecoratedOrbitAtom G sites A
      (B.map lpReplicaCurrentReflect.toEmbedding) q := by
  let target := lpReplicaPartialReflectProfile G sites m
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
    G sites q m hm L P
  let tag := lpReplicaTransportTag G sites relabel rawTag
  have hgate : LPReplicaRowGate G sites target A B tag := by
    exact lpReplicaRowGate_canonicalizeRawPartialReflect
      G sites q m hm L P rawTag A B hraw
  have htarget : lpReplicaSymmetrizedProfile G sites target = q :=
    (lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm
  let Ltarget : LPReplicaProfileOrbitLabel G sites q target :=
    lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L
  exact lpReplicaDecoratedOrbitAtomOfRowGate
    G sites target q tag A B htarget hgate Ltarget

set_option maxHeartbeats 1600000 in



noncomputable def lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtomRawBoundary
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k)
    (hcd : c ≠ d)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (hdisc :
      let target := lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
          (Finset.univ \ {d}))
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})
      let K' := lpReplicaPartialReflectCopiesRaw
        G sites z.1.1.1 {d} (Finset.univ \ {c})
      ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
      ((lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
              (lpReplicaThirdOfThree i j k u v) ∆
          lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).map
        lpReplicaCurrentReflect.toEmbedding) q := by
  exact lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
    G sites q z.1.1.1 z.1.1.2 z.2.2 {d}
      (lpReplicaSingletonFalseRowTag
        (lpReplicaPartialReflectCopyEquivRaw G sites z.1.1.1 {d} c))
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
            (lpReplicaThirdOfThree i j k u v) ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpReplicaOffdiagDecoratedSource_strictRoute_target_rowGate
        G sites hsite hij hik hjk hu hv huv q z c d hc hcd hfold hdisc)

set_option maxHeartbeats 1600000 in



noncomputable def lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k)
    (hcd : c ≠ d)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (hdisc :
      let target := lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
          (Finset.univ \ {d}))
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})
      let K' := lpReplicaPartialReflectCopiesRaw
        G sites z.1.1.1 {d} (Finset.univ \ {c})
      ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
            (lpReplicaThirdOfThree i j k u v) ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q := by
  let Sk := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k
  let Sl := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      (lpReplicaThirdOfThree i j k u v)
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let atom0 :=
    lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtomRawBoundary
      G sites hsite hij hik hjk hu hv huv q z c d hc hcd hfold hdisc
  have hfixed : (Sl ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sl ∆ T :=
    lpReplicaCurrentReflect_seam_symmDiff_ghost G sites
      (lpReplicaThirdOfThree i j k u v)
  exact cast (congrArg
    (fun D => LPReplicaDecoratedOrbitAtom G sites Sk D q) hfixed) atom0

end


end StatMech.Ising
