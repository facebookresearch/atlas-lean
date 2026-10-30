/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceUnprobedSite
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RayParityBdEdgeMatch

/-!
# Winding witnesses for boundary orbits

For a boundary orbit of a set `K` of sites, `mpl_orbitLoop K a` is the closed walk of faces to
the left of the darts of one period of the orbit. A site `z` is enclosed by a closed walk when the
horizontal ray going left from `z` crosses the walk an odd number of times
(`jec_rayCount z _` is odd). A *winding witness* for the orbit is a site of `K` enclosed by its
face loop.

This file proves that winding witnesses are preserved when a site that the orbit never probes is
removed, that ray counts are invariant under translation, and that every boundary orbit of a
single site has a winding witness. Removing unprobed sites one at a time then reduces the
existence of a winding witness for every orbit of every finite nonempty set to the *saturated*
case, where the orbit probes every site of `K` (`wei_WindingSaturatingWitness`).

That saturated statement is false: for the four neighbours of the origin the inner boundary
orbit probes all four sites, but its face loop encloses only the origin, which is not in the set.
This is proved here (`not_wei_WindingSaturatingWitness`), so the conditional results
`wei_windingWitness_of_descent` and `wei_starHull_windingWitness_of_residue` are vacuous.

## Main definitions

* `StatMech.Lattice.wei_WindingWitness K a`: some site of `K` has odd ray count with respect to
  the face loop of the orbit of `a`.
* `StatMech.Lattice.wei_WindingSaturatingWitness`: every orbit that probes all sites of a finite
  set with at least two sites has a winding witness (a false statement, see above).

## Main results

* `StatMech.Lattice.wei_windingWitness_transfer_diff_singleton`: a winding witness for the orbit
  in `K \ {c}` is one in `K` when the orbit never probes `c`.
* `StatMech.Lattice.wei_rayCount_trans`: ray counts of face loops are translation invariant.
* `StatMech.Lattice.wei_singleton_windingWitness`: every boundary orbit of a single site has a
  winding witness.
* `StatMech.Lattice.wei_windingWitness_of_descent`: the saturated case implies the general case
  (vacuous).
* `StatMech.Lattice.not_wei_WindingSaturatingWitness`: the saturated case is false.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The edges of the face loop of the orbit of `a`: the pairs of faces of consecutive darts in
one period. -/
theorem wei_mpl_orbitLoop_edges_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]

/-- Ray counts of closed walks depend only on their edge lists up to permutation. -/
theorem wei_rayCount_of_perm {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (Vc' : (hypercubicLattice 2).Walk b b) (z : Site 2)
    (hperm : List.Perm Vc.edges Vc'.edges) :
    jec_rayCount z Vc = jec_rayCount z Vc' := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact List.Perm.countP_eq _ hperm

/-- Ray counts of face loops agree for equal sets and equal base darts. -/
theorem wei_rayCount_congr (K K' : Set (Site 2)) (hKK : K = K')
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart K' e})
    (ha : a.1 = a'.1) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
  subst hKK
  rw [Subtype.ext ha]

/-- If the orbit of `a` never probes `c`, removing `c` from `K` does not change the edges of its
face loop. -/
theorem wei_loop_edges_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    (mpl_orbitLoop (K \ {c}) a').edges = (mpl_orbitLoop K a).edges := by
  rw [wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp]
  apply List.map_congr_left
  intro k _
  rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp k,
      bpc_iterate_dartNext_diff_singleton K c a.1 hnp (k + 1)]

/-- If the orbit of `a` never probes `c`, removing `c` from `K` does not change ray counts of its
face loop. -/
theorem wei_rayCount_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop (K \ {c}) a') = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_loop_edges_diff_singleton K c a a' hval hnp]

/-- A winding witness for the boundary orbit of `a`: a site of `K` whose ray count with respect to
the face loop of the orbit is odd, i.e. a site of `K` enclosed by the loop. -/
def wei_WindingWitness (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ z ∈ K, ¬ Even (jec_rayCount z (mpl_orbitLoop K a))

/-- A winding witness for the orbit of `a` in `K \ {c}` is a winding witness in `K`, when the
orbit never probes `c`. -/
theorem wei_windingWitness_transfer_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1))
    (hw : wei_WindingWitness (K \ {c}) a') :
    wei_WindingWitness K a := by
  obtain ⟨z, hzK', hzodd⟩ := hw
  refine ⟨z, ((Set.mem_sdiff _).mp hzK').1, ?_⟩
  rwa [wei_rayCount_diff_singleton K c a a' hval hnp z] at hzodd

/-- The face of a translated dart is the translated face. -/
theorem wei_dartFace_trans (w : Site 2) (e : Dart) :
    dartFace (transDart w e) = dartFace e + w := by
  unfold dartFace
  rw [transDart_tail, transDart_dir]
  funext i
  fin_cases i
  · change e.tail 0 + w 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0)
      = (e.tail 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0)) + w 0
    ring
  · change e.tail 1 + w 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1)
      = (e.tail 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1)) + w 1
    ring

/-- Ray edges are translation invariant. -/
theorem wei_rayEdge_trans (w z x y : Site 2) :
    jec_rayEdge (z + w) s(x + w, y + w) ↔ jec_rayEdge z s(x, y) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk]; simp only [Pi.add_apply]; omega

/-- Ray counts of face loops of boundary orbits are translation invariant. -/
theorem wei_rayCount_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a))
      = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [transSub_val, dartOrbitPeriod_trans]
  have hmap : (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext (transSet w K))^[k] (transDart w a.1)),
          dartFace ((dartNext (transSet w K))^[k + 1] (transDart w a.1))))
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1) + w,
          dartFace ((dartNext K)^[k + 1] a.1) + w)) := by
    apply List.map_congr_left
    intro k _
    rw [iterate_dartNext_trans, iterate_dartNext_trans, wei_dartFace_trans, wei_dartFace_trans]
  rw [hmap, List.countP_map, List.countP_map]
  apply List.countP_congr
  intro k _
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact wei_rayEdge_trans w z _ _

/-- The edges of the face loop of the unit cell orbit based at the second dart. -/
theorem wei_ucBase1_edges :
    (mpl_orbitLoop unitCell ucBase1).edges
      = [s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0]),
          s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase1_orbitPeriod]
  change ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart1),
      dartFace ((dartNext unitCell)^[k + 1] ucDart1)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart1) = ucDart1 from rfl, it1_1, it1_2, it1_3, it1_4]
  rw [mpl_dartFace_ucDart1, mpl_dartFace_ucDart2, mpl_dartFace_ucDart3, mpl_dartFace_ucDart0]

/-- The edges of the face loop of the unit cell orbit based at the third dart. -/
theorem wei_ucBase2_edges :
    (mpl_orbitLoop unitCell ucBase2).edges
      = [s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0]),
          s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase2_orbitPeriod]
  change ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart2),
      dartFace ((dartNext unitCell)^[k + 1] ucDart2)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart2) = ucDart2 from rfl, it2_1, it2_2, it2_3, it2_4]
  rw [mpl_dartFace_ucDart2, mpl_dartFace_ucDart3, mpl_dartFace_ucDart0, mpl_dartFace_ucDart1]

/-- The edges of the face loop of the unit cell orbit based at the fourth dart. -/
theorem wei_ucBase3_edges :
    (mpl_orbitLoop unitCell ucBase3).edges
      = [s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1]),
          s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase3_orbitPeriod]
  change ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart3),
      dartFace ((dartNext unitCell)^[k + 1] ucDart3)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart3) = ucDart3 from rfl, it3_1, it3_2, it3_3, it3_4]
  rw [mpl_dartFace_ucDart3, mpl_dartFace_ucDart0, mpl_dartFace_ucDart1, mpl_dartFace_ucDart2]

/-- For every base dart of the unit cell orbit, the origin has ray count one. -/
theorem wei_unitCell_basepoint_rayCount (b : {e : Dart // IsBoundaryDart unitCell e})
    (hb : b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) :
    jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell b) = 1 := by
  rcases hb with h | h | h | h
  · have hb0 : b = ucBase := Subtype.ext h
    rw [hb0]; exact mpl_unitCell_rayCount_eq_one
  · have hb1 : b = ucBase1 := Subtype.ext h
    rw [hb1, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase1) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase1_edges, jsf_unitCell_loop_edges]; decide
  · have hb2 : b = ucBase2 := Subtype.ext h
    rw [hb2, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase2) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase2_edges, jsf_unitCell_loop_edges]; decide
  · have hb3 : b = ucBase3 := Subtype.ext h
    rw [hb3, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase3) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase3_edges, jsf_unitCell_loop_edges]; decide

/-- Every boundary orbit of a single site has a winding witness: the site itself. -/
theorem wei_singleton_windingWitness (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    wei_WindingWitness ({v} : Set (Site 2)) a := by
  refine ⟨v, Set.mem_singleton _, ?_⟩
  obtain ⟨b, hbU, hval⟩ : ∃ b : {e : Dart // IsBoundaryDart unitCell e},
      (b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) ∧
        a.1 = transDart v b.1 := by
    rcases singleton_boundaryDart_eq_transDart v a.1 a.2 with
      ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · exact ⟨ucBase, Or.inl rfl, he⟩
    · exact ⟨ucBase2, Or.inr (Or.inr (Or.inl rfl)), he⟩
    · exact ⟨ucBase3, Or.inr (Or.inr (Or.inr rfl)), he⟩
    · exact ⟨ucBase1, Or.inr (Or.inl rfl), he⟩
  have hset : ({v} : Set (Site 2)) = transSet v unitCell := (transSet_unitCell v).symm
  have hcongr : jec_rayCount v (mpl_orbitLoop ({v} : Set (Site 2)) a)
      = jec_rayCount v (mpl_orbitLoop (transSet v unitCell) (transSub unitCell v b)) := by
    apply wei_rayCount_congr ({v} : Set (Site 2)) (transSet v unitCell) hset
    rw [hval, transSub_val]
  rw [hcongr]
  have hv0 : ((![0, 0] : Site 2) + v) = v := by funext i; fin_cases i <;> simp
  have htrans := wei_rayCount_trans unitCell v b (![0, 0] : Site 2)
  rw [hv0] at htrans
  rw [htrans, wei_unitCell_basepoint_rayCount b hbU]
  decide

/-- Every boundary orbit that probes every site of a finite set with at least two sites has a
winding witness.

This statement is false (`not_wei_WindingSaturatingWitness`): for `K` the four neighbours of the
origin and `a` a dart pointing into the origin, the orbit probes all of `K`, but its face loop is
the square around the origin, which encloses no site of `K`. Results assuming it are vacuous. -/
def wei_WindingSaturatingWitness : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a → wei_WindingWitness K a

/-- If every saturated orbit has a winding witness, every boundary orbit of every finite nonempty
set does (induction on the number of sites, removing a site the orbit never probes).

The hypothesis `wei_WindingSaturatingWitness` is false (`not_wei_WindingSaturatingWitness`), so
this result is vacuous; its conclusion fails for the inner orbit of a set with a hole. -/
theorem wei_windingWitness_of_descent (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : wei_WindingWitness K a := by
  generalize hn : K.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n IH =>
    subst hn
    rcases Nat.lt_or_ge K.ncard 2 with hlt | hge
    · have h1 : K.ncard = 1 := by
        have hpos : 0 < K.ncard := (Set.ncard_pos hK).mpr hne
        omega
      obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
      subst hv
      exact wei_singleton_windingWitness v a
    · by_cases hsat : K ⊆ bpc_orbitFootprint K a
      · exact hres K hK hge a hsat
      · rw [Set.not_subset] at hsat
        obtain ⟨c, hcK, hc⟩ := hsat
        have hne_tail : c ≠ a.1.tail := bpc_ne_tail_of_not_footprint K a c hc
        have hbd : IsBoundaryDart (K \ {c}) a.1 :=
          bpc_isBoundaryDart_diff_singleton K c a.1 a.2 hne_tail
        set a' : {e : Dart // IsBoundaryDart (K \ {c}) e} := ⟨a.1, hbd⟩ with ha'
        have hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1) :=
          bpc_notProbed_of_not_footprint K a c hc
        have hK' : (K \ {c}).Finite := hK.subset Set.sdiff_subset
        have hcard_eq : (K \ {c}).ncard = K.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hcK
        have hne' : (K \ {c}).Nonempty := by
          rw [← Set.ncard_pos hK', hcard_eq]; omega
        have hncard_lt : (K \ {c}).ncard < K.ncard := by rw [hcard_eq]; omega
        have hw' : wei_WindingWitness (K \ {c}) a' :=
          IH (K \ {c}).ncard hncard_lt (K \ {c}) hK' hne' a' rfl
        exact wei_windingWitness_transfer_diff_singleton K c a a' (by rw [ha']) hnp hw'

/-- Star hull form of `wei_windingWitness_of_descent`; vacuous for the same reason. -/
theorem wei_starHull_windingWitness_of_residue (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  wei_windingWitness_of_descent hres (ndt_StarHull K) hSK hne a

/-- If one site `z0` of `K` is enclosed by the face loop and every site of `K` is joined to `z0` by
a walk avoiding the loop, every site of `K` is enclosed. -/
theorem wei_insideHalf_of_windingWitness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {z0 : Site 2} (_hz0 : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  intro z hz
  obtain ⟨p, hp⟩ := hInt z hz
  exact ooi_odd_of_connected_to_odd (mpl_orbitLoop K a) p hp hodd0

/-- The boundary orbit of the unit cell has a winding witness, the origin. -/
theorem wei_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  refine ⟨![0, 0], ?_, ?_⟩
  · simp only [unitCell, Set.mem_singleton_iff]
  · rw [mpl_unitCell_rayCount_eq_one]; decide

/-- The successor of a dart pointing into the hole of `bpc_holeRing` has its tail rotated a quarter
turn counterclockwise. -/
theorem wei_holeDart_next_tail {e : Dart} (he : bpc_HoleDart e) :
    (dartNext bpc_holeRing e).tail = rot90Fun e.tail := by
  rw [dartNext_of_front_mem bpc_holeRing e (bpc_holeDart_front he), mkDart_tail,
    Dart.dir_def, he.1, zero_add, zero_sub, rot90Fun_neg, neg_neg]

/-- Along the orbit around the hole of `bpc_holeRing`, the tail after `k` steps is the initial tail
rotated by `k` quarter turns. -/
theorem wei_holeDart_iterate_tail {e : Dart} (he : bpc_HoleDart e) (k : ℕ) :
    ((dartNext bpc_holeRing)^[k] e).tail = rot90Fun^[k] e.tail := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', wei_holeDart_next_tail (bpc_holeDart_iterate he n), ih,
      Function.iterate_succ_apply']

/-- Two darts pointing into the hole of `bpc_holeRing` with the same tail are equal. -/
theorem wei_holeDart_eq {d e : Dart} (hd : bpc_HoleDart d) (he : bpc_HoleDart e)
    (h : d.tail = e.tail) : d = e :=
  Dart.ext h (hd.1.trans he.1.symm)

/-- The face of a dart pointing into the hole of `bpc_holeRing`, in terms of its tail. -/
theorem wei_holeDart_face {e : Dart} (he : bpc_HoleDart e) :
    dartFace e = ![e.tail 0 + negPart (-e.tail 0) + negPart (e.tail 1),
      e.tail 1 + negPart (-e.tail 1) + negPart (-e.tail 0)] := by
  have hdir : e.dir = -e.tail := by rw [Dart.dir_def, he.1, zero_sub]
  unfold dartFace
  rw [hdir]
  simp [rot90Fun]

/-- The tails along the orbit of `bpc_holeBase` are the quarter-turn rotations of `(1, 0)`. -/
theorem wei_holeBase_iterate_tail (k : ℕ) :
    ((dartNext bpc_holeRing)^[k] bpc_holeBase.1).tail = rot90Fun^[k] ![1, 0] := by
  rw [show bpc_holeBase.1 = bpc_holeDart0 from rfl, wei_holeDart_iterate_tail bpc_holeDart0_hole k]
  rfl

/-- The orbit around the hole of `bpc_holeRing` has length four. -/
theorem wei_holeBase_period : dartOrbitPeriod bpc_holeRing bpc_holeBase = 4 := by
  have hper : Function.IsPeriodicPt (dartNextSub bpc_holeRing) 4 bpc_holeBase := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    apply wei_holeDart_eq (bpc_holeDart_iterate bpc_holeDart0_hole 4) bpc_holeDart0_hole
    rw [wei_holeDart_iterate_tail bpc_holeDart0_hole, rot90Fun_iterate_four_eq]
  have hdvd : dartOrbitPeriod bpc_holeRing bpc_holeBase ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hper
  have h1 := one_lt_dartOrbitPeriod bpc_holeRing bpc_holeRing_finite bpc_holeBase
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hmin := Function.isPeriodicPt_minimalPeriod (dartNextSub bpc_holeRing) bpc_holeBase
  change Function.IsPeriodicPt _ (dartOrbitPeriod bpc_holeRing bpc_holeBase) _ at hmin
  interval_cases h : dartOrbitPeriod bpc_holeRing bpc_holeBase
  · exfalso
    have h2 := congrArg (fun a => a.1.tail 0) hmin
    simp only [dartNextSub_iterate_val, wei_holeBase_iterate_tail] at h2
    simp [rot90Fun, show bpc_holeBase.1 = bpc_holeDart0 from rfl, bpc_holeDart0] at h2
  · exact absurd hdvd (by decide)
  · rfl

/-- The face loop of the orbit around the hole of `bpc_holeRing` is the unit square of faces around
the origin. -/
theorem wei_holeBase_loop_edges :
    (mpl_orbitLoop bpc_holeRing bpc_holeBase).edges =
      [s((![0, -1] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![-1, 0]),
        s((![-1, 0] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![0, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, wei_holeBase_period]
  have hf : ∀ k, dartFace ((dartNext bpc_holeRing)^[k] bpc_holeBase.1) =
      ![(rot90Fun^[k] ![1, 0]) 0 + negPart (-(rot90Fun^[k] ![1, 0]) 0)
          + negPart ((rot90Fun^[k] ![1, 0]) 1),
        (rot90Fun^[k] ![1, 0]) 1 + negPart (-(rot90Fun^[k] ![1, 0]) 1)
          + negPart (-(rot90Fun^[k] ![1, 0]) 0)] := by
    intro k
    rw [show bpc_holeBase.1 = bpc_holeDart0 from rfl,
      wei_holeDart_face (bpc_holeDart_iterate bpc_holeDart0_hole k),
      wei_holeDart_iterate_tail bpc_holeDart0_hole k]
    rfl
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, hf]
  simp [rot90Fun, negPart]

/-- `wei_WindingSaturatingWitness` is false. The orbit around the hole of `bpc_holeRing` (the four
neighbours of the origin) probes all four sites, but its face loop is the square around the origin,
and every site of `bpc_holeRing` has even ray count with respect to it. -/
theorem not_wei_WindingSaturatingWitness : ¬ wei_WindingSaturatingWitness := by
  classical
  intro h
  have hcard : 2 ≤ bpc_holeRing.ncard := by
    refine (Set.one_lt_ncard bpc_holeRing_finite).mpr ⟨![1, 0], ?_, ![0, 1], ?_, ?_⟩
    · unfold bpc_holeRing; simp
    · unfold bpc_holeRing; simp
    · intro h; have := congrFun h 0; simp at this
  have htail : ∀ i : ℕ, ((dartNext bpc_holeRing)^[i] bpc_holeBase.1).tail ∈
      bpc_orbitFootprint bpc_holeRing bpc_holeBase := fun i => ⟨i, Or.inr (Or.inr rfl)⟩
  have hsat : bpc_holeRing ⊆ bpc_orbitFootprint bpc_holeRing bpc_holeBase := by
    intro x hx
    unfold bpc_holeRing at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have := htail 0; rwa [wei_holeBase_iterate_tail] at this
    · have := htail 1; rw [wei_holeBase_iterate_tail] at this
      convert this using 1; ext j; fin_cases j <;> simp [rot90Fun]
    · have := htail 2; rw [wei_holeBase_iterate_tail] at this
      convert this using 1; ext j; fin_cases j <;> simp [rot90Fun]
    · have := htail 3; rw [wei_holeBase_iterate_tail] at this
      convert this using 1; ext j; fin_cases j <;> simp [rot90Fun]
  obtain ⟨z, hz, hodd⟩ := h _ bpc_holeRing_finite hcard bpc_holeBase hsat
  rw [jec_rayCount, wei_holeBase_loop_edges] at hodd
  unfold bpc_holeRing at hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [jec_rayEdge_mk] at hodd

end Lattice

end StatMech
