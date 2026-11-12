/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictIncidence








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveDisconnectionDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _




theorem lpReplicaPartialReflectCopiesRaw_sdiff_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (d c : Copy (lpReplicaCurrentGraph G sites) m) :
    let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
    lpReplicaPartialReflectCopiesRaw G sites m {d}
        (Finset.univ \ {c}) =
      Finset.univ \ {R c} := by
  classical
  dsimp only
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  ext e
  simp only [lpReplicaPartialReflectCopiesRaw, Finset.mem_map,
    Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨x, hxc, rfl⟩
    exact fun h => hxc (R.injective h)
  · intro hec
    refine ⟨R.symm e, ?_, R.apply_symm_apply e⟩
    intro h
    apply hec
    simpa using congrArg R h





theorem lpReplica_partialReflect_strictMatchingRoute_ghost_disconnected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (B : Finset (LPReplicaCurrentVertex V))
    (d : Copy (lpReplicaCurrentGraph G sites) m)
    (hdK : d ∈ K)
    (hsupport : K.biUnion (fun e =>
      (endsM (lpReplicaCurrentGraph G sites) m e).toFinset) = B)
    (hunique : ∀ x ∈ B,
      ∃! e, e ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
    (hg0B : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ B)
    (hg1B : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ B)
    {u v : I} (huv : u ≠ v)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v))) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let K' := lpReplicaPartialReflectCopiesRaw G sites m {d} K
    ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let E := endsM H m
  let target := lpReplicaCollisionProfile G sites
    (profileFlux H m (Finset.univ \ {d}))
    (profileFlux H m {d})
  let E' := endsM H target
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  let d' := R d
  let T := lpReplicaPartialReflectCopiesRaw G sites m {d} (K \ {d})
  have hsplit : lpReplicaPartialReflectCopiesRaw G sites m {d} K =
      insert d' T := by
    unfold T d' R lpReplicaPartialReflectCopiesRaw
    calc
      Finset.map
          (lpReplicaPartialReflectCopyEquivRaw G sites m {d}).toEmbedding K =
          Finset.map
            (lpReplicaPartialReflectCopyEquivRaw G sites m {d}).toEmbedding
            (insert d (K \ {d})) := by
              rw [Finset.insert_sdiff_self_of_mem hdK]
      _ = insert
          (lpReplicaPartialReflectCopyEquivRaw G sites m {d} d)
          (Finset.map
            (lpReplicaPartialReflectCopyEquivRaw G sites m {d}).toEmbedding
            (K \ {d})) := Finset.map_insert _ _ _
  have hbase (x y : LPReplicaCurrentVertex V) :
      connK E' T x y ↔ connK E (K \ {d}) x y := by
    simpa only [E', E, T, target, H] using
      (lpReplicaPartialReflectCopiesRaw_connK_of_disjoint
        G sites m {d} (K \ {d}) (by simp) x y)
  have hd'ends : E' d' = Sym2.map lpReplicaCurrentReflect (E d) := by
    simpa only [E', E, d', R, target, H] using
      (lpReplicaPartialReflectCopyEquivRaw_ends_of_mem
        G sites m {d} d (by simp))
  have hmono : K \ {d} ⊆ K := Finset.sdiff_subset
  have hsame :=
    lpReplicaCurrentEdge_sameSide_of_fold_eq_distinct_sites
      G sites hsite d.1 huv hfold
  intro hconn
  rw [hsplit] at hconn
  rcases randomCurrent_connK_insert_edge_cases E' T d' hconn with
      hbaseGhost | ⟨x, hxd, y, hyd, hg0x, hyg1⟩
  · have hsource : connK E K
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1 :=
      StatMech.GrahamGHS.FourColor.connK_mono hmono
        ((hbase _ _).mp hbaseGhost)
    rcases randomCurrent_connK_eq_or_common_edge_of_unique_incidence
        E K B hsupport hunique hg0B hsource with hghost | ⟨e, heK, he0, he1⟩
    · exact (by
        simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hghost)
    · have hedge : e.1.1 =
          s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
            lpReplicaCurrentGhost1) :=
        sym2_eq_mk_of_mem_of_mem_of_ne he0 he1 (by
          simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
      have heGraph := SimpleGraph.mem_edgeFinset.mp e.1.2
      rw [hedge] at heGraph
      simpa [H, lpReplicaCurrentGraph, lpReplicaCurrentRel,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using heGraph
  · have hg0xSource : connK E K
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) x :=
      StatMech.GrahamGHS.FourColor.connK_mono hmono
        ((hbase _ _).mp hg0x)
    have hyg1Source : connK E K y
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) :=
      StatMech.GrahamGHS.FourColor.connK_mono hmono
        ((hbase _ _).mp hyg1)
    have hxPhysical : x ≠
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) := by
      intro hx0
      subst x
      rw [hd'ends] at hxd
      rcases hsame with ⟨p, q, hd⟩ | ⟨p, q, hd⟩ <;>
        simp [E, endsM, hd, lpReplicaCurrentReflect,
          lpReplicaCurrentGhost0] at hxd
    have hyPhysical : y ≠
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) := by
      intro hy1
      subst y
      rw [hd'ends] at hyd
      rcases hsame with ⟨p, q, hd⟩ | ⟨p, q, hd⟩ <;>
        simp [E, endsM, hd, lpReplicaCurrentReflect,
          lpReplicaCurrentGhost1] at hyd
    have hxLeft : ∃ w : V,
        x = (.inl (.inl w) : LPReplicaCurrentVertex V) := by
      rcases randomCurrent_connK_eq_or_common_edge_of_unique_incidence
          E K B hsupport hunique hg0B hg0xSource with hx0 | ⟨e, heK, he0, hex⟩
      · exact False.elim (hxPhysical hx0.symm)
      · obtain ⟨w, he⟩ := lpReplicaCurrentEdge_eq_ghost0_left_of_mem
          G sites e.1 e.1.2 he0
        change x ∈ e.1.1 at hex
        rw [he, Sym2.mem_iff] at hex
        rcases hex with hex | hex
        · exact False.elim (hxPhysical hex)
        · exact ⟨w, hex⟩
    have hyRight : ∃ w : V,
        y = (.inl (.inr w) : LPReplicaCurrentVertex V) := by
      have hg1ySource : connK E K
          (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) y :=
        connK_symm E K hyg1Source
      rcases randomCurrent_connK_eq_or_common_edge_of_unique_incidence
          E K B hsupport hunique hg1B hg1ySource with hy1 | ⟨e, heK, he1, hey⟩
      · exact False.elim (hyPhysical hy1.symm)
      · obtain ⟨w, he⟩ := lpReplicaCurrentEdge_eq_ghost1_right_of_mem
          G sites e.1 e.1.2 he1
        change y ∈ e.1.1 at hey
        rw [he, Sym2.mem_iff] at hey
        rcases hey with hey | hey
        · exact False.elim (hyPhysical hey)
        · exact ⟨w, hey⟩
    obtain ⟨px, rfl⟩ := hxLeft
    obtain ⟨py, rfl⟩ := hyRight
    rw [hd'ends] at hxd hyd
    rcases hsame with ⟨p, q, hd⟩ | ⟨p, q, hd⟩ <;>
      simp [E, endsM, hd, lpReplicaCurrentReflect] at hxd hyd

end

end StatMech.Ising
