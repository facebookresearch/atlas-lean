/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveAggregateStrictRouteDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


structure LPReplicaAggregateRankFiveStrictRouteData
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (a : LPReplicaAggregateDecoratedSource G sites q) (k : I) where
  c : Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  d : Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  u : I
  v : I
  hc : c.1.1 = lpReplicaCurrentSeamEdge sites k
  hdK : d ∈ Finset.univ \ {c}
  hu : u = a.1 ∨ u = a.2.1 ∨ u = k
  hv : v = a.1 ∨ v = a.2.1 ∨ v = k
  huv : u ≠ v
  hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
    s(Sum.inl (sites u), Sum.inl (sites v))
  hl : let l := lpReplicaThirdOfThree a.1 a.2.1 k u v
    l ≠ u ∧ l ≠ v ∧ (l = a.1 ∨ l = a.2.1 ∨ l = k)
  hdisc :
    let m := a.2.2.2.1.1.1
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let K' := lpReplicaPartialReflectCopiesRaw
      G sites m {d} (Finset.univ \ {c})
    ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1



theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_disconnected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    Nonempty (LPReplicaAggregateRankFiveStrictRouteData G sites q a k) := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching
      G sites hsite q hcard z
  dsimp only at hpm
  obtain ⟨c, hc, hKcard, hsources, hsupport, hunique⟩ := hpm
  let K := Finset.univ \ {c}
  let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  obtain ⟨d, hdK, hd0, hd1, hddiag⟩ :=
    lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
      G sites hsite hij hik hjk a.2.2.2.1.1.1 K hKcard hsupport hunique
        (fun e _ => hunmarked.2.1 e) (fun e _ => hunmarked.2.2 e)
  obtain ⟨u, v, hu, hv, huv, hfold⟩ :=
    lpReplica_strictPhysicalRoute_folded_labels G sites hsite
      hij hik hjk a.2.2.2.1.1.1 K hsupport d hdK hd0 hd1 hddiag
  have hl := lpReplicaThirdOfThree_spec hij hik hjk hu hv huv
  have hdisc :=
    lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected
      G sites hsite a.2.2.2.1.1.1 K
        (lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k) d hdK
        hsupport hunique
        (lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
          sites a.1 a.2.1 k)
        (lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
          sites a.1 a.2.1 k)
        huv hfold
  exact ⟨{
    c := c
    d := d
    u := u
    v := v
    hc := hc
    hdK := hdK
    hu := hu
    hv := hv
    huv := huv
    hfold := hfold
    hl := hl
    hdisc := hdisc
  }⟩


noncomputable def lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteData
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    LPReplicaAggregateRankFiveStrictRouteData G sites q a k := by
  dsimp only
  exact Classical.choice
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_disconnected
      G sites hsite q hcard z)



noncomputable def lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    LPReplicaAggregateDecoratedTarget G sites q := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let route :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteData
      G sites hsite q hcard z
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hdc : route.d ≠ route.c := by
    exact (Finset.mem_sdiff.mp route.hdK).2 ∘ Finset.mem_singleton.mpr
  let l := lpReplicaThirdOfThree a.1 a.2.1 k route.u route.v
  let atom := lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom
    G sites hsite hij hik hjk route.hu route.hv route.huv q a.2.2.2
      route.c route.d route.hc hdc.symm route.hfold route.hdisc
  exact ⟨0, ⟨k, ⟨l, atom⟩⟩⟩

@[simp] theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget_selectedSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget
      G sites hsite q hcard z).2.1 =
      lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
        (z.toAggregate G sites q) := by
  classical
  unfold lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget
  dsimp only

end

end StatMech.Ising
