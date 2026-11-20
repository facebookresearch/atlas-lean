/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveDisconnection








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRouteFullSourcesDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaOffdiagDecoratedSource_strictRoute_target_fullSources
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v))) :
    let l := lpReplicaThirdOfThree i j k u v
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) target) Finset.univ =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) l ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let E := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let Sk := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k
  let Su := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) u
  let Sv := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) v
  let S := fun t : I => lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) t
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hddiag : ¬ (E d).IsDiag := by
    exact endsM_not_isDiag (G := lpReplicaCurrentGraph G sites)
      z.1.1.1 d
  have hsingle : RandomCurrent.sources E {d} = (E d).toFinset :=
    randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag
      E d hddiag
  have hmap : (E d).toFinset.map
        lpReplicaCurrentReflect.toEmbedding =
      (Sym2.map lpReplicaCurrentReflect (E d)).toFinset := by
    exact (sym2_toFinset_map_embedding lpReplicaCurrentReflect
      lpReplicaCurrentReflect.toEmbedding.injective (E d)).symm
  have htoggle : (E d).toFinset ∆
        (Sym2.map lpReplicaCurrentReflect (E d)).toFinset = Su ∆ Sv := by
    simpa only [E, Su, Sv, endsM] using
      (lpReplicaCurrentEdge_toFinset_symmDiff_reflect_eq_seams
        G sites hsite d.1 huv hfold)
  have hthird := lpReplica_threeSeam_toggle_two_eq_selected_third
    S T hij hik hjk hu hv huv
  rw [lpReplicaPartialReflectCopiesRaw_univ_sources,
    StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp),
    lpReplicaOffdiagDecoratedSource_fullRawSources G sites q z,
    hsingle, hmap]
  change (Si ∆ Sj ∆ T ∆ (E d).toFinset) ∆
      (Sym2.map lpReplicaCurrentReflect (E d)).toFinset = _
  calc
    (Si ∆ Sj ∆ T ∆ (E d).toFinset) ∆
        (Sym2.map lpReplicaCurrentReflect (E d)).toFinset =
        Si ∆ Sj ∆ T ∆
          ((E d).toFinset ∆
            (Sym2.map lpReplicaCurrentReflect (E d)).toFinset) := by
              rw [symmDiff_assoc]
    _ = Si ∆ Sj ∆ T ∆ (Su ∆ Sv) := by rw [htoggle]
    _ = Sk ∆ S (lpReplicaThirdOfThree i j k u v) ∆ T := by
      simpa only [S, Si, Sj, Sk, Su, Sv] using hthird

end

end StatMech.Ising
