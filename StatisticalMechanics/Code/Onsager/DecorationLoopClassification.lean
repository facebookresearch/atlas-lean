/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationLoopWalk










namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_isPath_eq_of_edges_toFinset_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    p = q := by
  induction p with
  | nil =>
      have hqEmpty : q.edges.toFinset = ∅ := by
        simpa using hedges.symm
      have hqEdges : q.edges = [] :=
        (List.toFinset_eq_empty_iff q.edges).mp hqEmpty
      have hqnil : q.Nil := SimpleGraph.Walk.edges_eq_nil.mp hqEdges
      exact hqnil.eq_nil.symm
  | @cons u w v huw p ih =>
      cases q with
      | nil =>
          have hedge : s(u, w) ∈
              (SimpleGraph.Walk.cons huw p).edges.toFinset := by simp
          rw [hedges] at hedge
          simpa using hedge
      | @cons _ w' _ huw' q =>
          have hedgeP : s(u, w) ∈
              (SimpleGraph.Walk.cons huw p).edges.toFinset := by simp
          have hedgeQ : s(u, w) ∈
              (SimpleGraph.Walk.cons huw' q).edges := by
            exact List.mem_toFinset.mp (hedges ▸ hedgeP)
          have hw : w' = w := by
            have hsnd := hq.eq_snd_of_mem_edges hedgeQ
            simpa using hsnd.symm
          subst w'
          have hpTail : p.IsPath := by
            simpa using hp.tail
          have hqTail : q.IsPath := by
            simpa using hq.tail
          have hpnList : s(u, w) ∉ p.edges := by
            have hnodup := hp.isTrail.edges_nodup
            rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
            exact hnodup.1
          have hqnList : s(u, w) ∉ q.edges := by
            have hnodup := hq.isTrail.edges_nodup
            rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
            exact hnodup.1
          have htailEdges : p.edges.toFinset = q.edges.toFinset := by
            have herase := congrArg
              (Finset.erase · s(u, w)) hedges
            simp only [SimpleGraph.Walk.edges_cons,
              List.toFinset_cons] at herase
            rw [Finset.erase_insert
                (mt List.mem_toFinset.mp hpnList),
              Finset.erase_insert
                (mt List.mem_toFinset.mp hqnList)] at herase
            exact herase
          have hpq : p = q := ih q hpTail hqTail htailEdges
          subst q
          rfl

theorem ons_rooted_isCycle_eq_of_snd_edges_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (p q : G.Walk u u) (hp : p.IsCycle) (hq : q.IsCycle)
    (hsnd : p.snd = q.snd)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    p = q := by
  have hpne : ¬p.Nil := hp.not_nil
  have hqne : ¬q.Nil := hq.not_nil
  let edge : Sym2 V := s(u, p.snd)
  let qtail : G.Walk p.snd u := q.tail.copy hsnd.symm rfl
  have hpNot : edge ∉ p.tail.edges := by
    have hnodup := hp.edges_nodup
    rw [← p.cons_tail_eq hpne,
      SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
    exact hnodup.1
  have hqNot : edge ∉ q.tail.edges := by
    have hnodup := hq.edges_nodup
    rw [← q.cons_tail_eq hqne,
      SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
    simpa [edge, hsnd] using hnodup.1
  have htailEdges : p.tail.edges.toFinset = qtail.edges.toFinset := by
    have hedges' := hedges
    rw [← p.cons_tail_eq hpne, ← q.cons_tail_eq hqne,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
      List.toFinset_cons, List.toFinset_cons] at hedges'
    have hedgeSnd : s(u, q.snd) = edge := by
      rw [← hsnd]
    rw [hedgeSnd] at hedges'
    change insert edge p.tail.edges.toFinset =
      insert edge q.tail.edges.toFinset at hedges'
    have herase := congrArg (Finset.erase · edge) hedges'
    change (insert edge p.tail.edges.toFinset).erase edge =
      (insert edge q.tail.edges.toFinset).erase edge at herase
    rw [Finset.erase_insert (mt List.mem_toFinset.mp hpNot),
      Finset.erase_insert (mt List.mem_toFinset.mp hqNot)] at herase
    simpa [qtail, SimpleGraph.Walk.edges_copy] using herase
  have hqtailPath : qtail.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy q.tail hsnd.symm rfl).mpr
      hq.isPath_tail
  have htail : p.tail = qtail :=
    ons_isPath_eq_of_edges_toFinset_eq p.tail qtail
      hp.isPath_tail hqtailPath htailEdges
  have htailHEq : p.tail ≍ q.tail := by
    apply (heq_of_eq htail).trans
    simp [qtail, SimpleGraph.Walk.copy]
  have hcons :
      SimpleGraph.Walk.cons (p.adj_snd hpne) p.tail =
        SimpleGraph.Walk.cons (q.adj_snd hqne) q.tail := by
    rw [SimpleGraph.Walk.cons.injEq]
    exact ⟨hsnd, htailHEq⟩
  calc
    p = SimpleGraph.Walk.cons (p.adj_snd hpne) p.tail :=
      (p.cons_tail_eq hpne).symm
    _ = SimpleGraph.Walk.cons (q.adj_snd hqne) q.tail := hcons
    _ = q := q.cons_tail_eq hqne

theorem ons_decCycleDartList_copy
    {L : ℕ} {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (h : d = e) :
    ons_decCycleDartList (q.copy h h) = ons_decCycleDartList q := by
  subst e
  rfl

theorem ons_squarefree_valid_loop_eq_of_zero_eq
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d e : Fin n → ons_Dart L)
    (hdvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hevalid : ∀ k : Fin n,
      (e k).1 = ons_dirStep L (e (k + 1)).2 (e (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hdexp : ons_decLoopExponent L d = ons_finsetExponent S)
    (heexp : ons_decLoopExponent L e = ons_finsetExponent S)
    (hzero : d 0 = e 0) :
    d = e := by
  let qd := ons_decLoopWalk L d hdvalid
  let qe := ons_decLoopWalk L e hevalid
  let qe' : (ons_decGraph L).Walk (d 0) (d 0) :=
    qe.copy hzero.symm hzero.symm
  have hqd : qd.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hdvalid S hdexp
  have hqe : qe.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L e hevalid S heexp
  have hqe' : qe'.IsCycle := by
    exact (SimpleGraph.Walk.isCycle_copy qe hzero.symm).mpr hqe
  have hsnd : qd.snd = qe'.snd := by
    change qd.getVert 1 = qe'.getVert 1
    rw [show qd.getVert 1 = qd.snd from rfl,
      show qe'.getVert 1 = qe'.snd from rfl,
      ons_decLoopWalk_snd L d hdvalid]
    change ons_dartRev L (d 0) = (qe.copy hzero.symm hzero.symm).getVert 1
    rw [SimpleGraph.Walk.getVert_copy]
    change ons_dartRev L (d 0) = qe.snd
    rw [ons_decLoopWalk_snd L e hevalid, hzero]
  have hedges : qd.edges.toFinset = qe'.edges.toFinset := by
    rw [show qd.edges.toFinset = S from
      ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hdvalid S hdexp]
    rw [SimpleGraph.Walk.edges_copy]
    exact (ons_decLoopWalk_edges_toFinset_of_squarefree
      L e hevalid S heexp).symm
  have hq : qd = qe' :=
    ons_rooted_isCycle_eq_of_snd_edges_eq qd qe' hqd hqe' hsnd hedges
  apply List.ofFn_injective
  rw [← ons_decLoopWalk_cycleDartList L d hdvalid,
    ← ons_decLoopWalk_cycleDartList L e hevalid]
  calc
    ons_decCycleDartList qd = ons_decCycleDartList qe' :=
      congrArg ons_decCycleDartList hq
    _ = ons_decCycleDartList qe :=
      ons_decCycleDartList_copy qe hzero.symm

noncomputable def ons_decLoopExternalExponent
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_DecEdge L →₀ ℕ :=
  ∑ k, Finsupp.single s(d k, ons_dartRev L (d k)) 1

noncomputable def ons_decLoopInternalExponent
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_DecEdge L →₀ ℕ :=
  ∑ k, ∑ i ∈ ons_decChainPathIndices ((d (k + 1)).2 + 2) (d k).2,
    Finsupp.single (ons_decChainEdge (d k).1 i) 1

theorem ons_decChainPathIndices_comm (a b : Fin 4) :
    ons_decChainPathIndices a b = ons_decChainPathIndices b a := by
  ext i
  simp only [ons_decChainPathIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  tauto

theorem ons_decLoopExponent_eq_external_add_internal
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopExponent L d =
      ons_decLoopExternalExponent L d +
        ons_decLoopInternalExponent L d := by
  unfold ons_decLoopExponent ons_decTransitionExponent
    ons_decLoopExternalExponent ons_decLoopInternalExponent
  rw [Finset.sum_add_distrib]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
    (fun k ↦ Finsupp.single s(d k, ons_dartRev L (d k)) 1)

theorem ons_decLoopExponent_rotate
    (L : ℕ) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L) (r : Fin n) :
    ons_decLoopExponent L (ons_rotate r d) =
      ons_decLoopExponent L d := by
  unfold ons_decLoopExponent
  simpa [ons_rotate, add_assoc, add_comm, add_left_comm] using
    Equiv.sum_comp (Equiv.addRight r)
      (fun k : Fin n ↦
        ons_decTransitionExponent L (d k) (d (k + 1)))

theorem ons_decLoopScalar_rotate
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) (r : Fin n) :
    ons_decLoopScalar L omega u v (ons_rotate r d) =
      ons_decLoopScalar L omega u v d := by
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_decLoopScalar_eq_loopWeight_one]
  exact ons_loopWeight_rotate
    (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v) r d

theorem ons_decLoopExternalExponent_loopRev
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopExternalExponent L (ons_loopRev L d) =
      ons_decLoopExternalExponent L d := by
  unfold ons_decLoopExternalExponent ons_loopRev
  calc
    (∑ k : Fin n, Finsupp.single
        s(ons_dartRev L (d (-k)),
          ons_dartRev L (ons_dartRev L (d (-k)))) 1) =
        ∑ k : Fin n, Finsupp.single
          s(d (-k), ons_dartRev L (d (-k))) 1 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ons_dartRev_involutive, Sym2.eq_swap]
    _ = ∑ k : Fin n, Finsupp.single
          s(d k, ons_dartRev L (d k)) 1 :=
      Equiv.sum_comp (Equiv.neg (Fin n))
        (fun k ↦ Finsupp.single s(d k, ons_dartRev L (d k)) 1)

theorem ons_decLoopInternalExponent_loopRev
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopInternalExponent L (ons_loopRev L d) =
      ons_decLoopInternalExponent L d := by
  unfold ons_decLoopInternalExponent
  let e : Fin n ≃ Fin n :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  calc
    (∑ k : Fin n,
      ∑ i ∈ ons_decChainPathIndices
          ((ons_loopRev L d (k + 1)).2 + 2)
          (ons_loopRev L d k).2,
        Finsupp.single
          (ons_decChainEdge (ons_loopRev L d k).1 i) 1) =
        ∑ k : Fin n,
          ∑ i ∈ ons_decChainPathIndices
              ((d (e k + 1)).2 + 2) (d (e k)).2,
            Finsupp.single (ons_decChainEdge (d (e k)).1 i) 1 := by
      apply Finset.sum_congr rfl
      intro k hk
      have he : e k = -(k + 1) := rfl
      rw [he]
      have hidx : -(k + 1) + 1 = -k := by abel
      have hsite := hvalid (-(k + 1))
      rw [hidx] at hsite
      simp only [ons_loopRev, ons_dartRev, Prod.snd, Prod.fst]
      simp only [add_assoc]
      rw [show (2 + 2 : Fin 4) = 0 by decide, add_zero]
      rw [hidx, ← hsite, ons_decChainPathIndices_comm]
    _ = ∑ k : Fin n,
          ∑ i ∈ ons_decChainPathIndices
              ((d (k + 1)).2 + 2) (d k).2,
            Finsupp.single (ons_decChainEdge (d k).1 i) 1 :=
      Equiv.sum_comp e
        (fun k : Fin n ↦
          ∑ i ∈ ons_decChainPathIndices
              ((d (k + 1)).2 + 2) (d k).2,
            Finsupp.single (ons_decChainEdge (d k).1 i) 1)

theorem ons_decLoopExponent_loopRev
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopExponent L (ons_loopRev L d) =
      ons_decLoopExponent L d := by
  rw [ons_decLoopExponent_eq_external_add_internal,
    ons_decLoopExponent_eq_external_add_internal,
    ons_decLoopExternalExponent_loopRev,
    ons_decLoopInternalExponent_loopRev L d hvalid]

theorem ons_decLoopScalar_loopRev_spin
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) (ons_loopRev L d) =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d := by
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_decLoopScalar_eq_loopWeight_one,
    ons_KWmatWeightedPhase_const]
  exact ons_loopWeight_spinPhase_loopRev
    (1 : ℂ) ons_turnRoot ons_turnRoot_sq a b d

noncomputable def ons_decSquarefreeLoopFinset
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L)) :
    Finset (Fin n → ons_Dart L) :=
  Finset.univ.filter fun d ↦
    ons_decLoopExponent L d = ons_finsetExponent S ∧
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0

theorem ons_mem_decSquarefreeLoopFinset
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    (d : Fin n → ons_Dart L) :
    d ∈ ons_decSquarefreeLoopFinset L a b S ↔
      ons_decLoopExponent L d = ons_finsetExponent S ∧
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0 := by
  simp [ons_decSquarefreeLoopFinset]

theorem ons_decSquarefreeLoop_eval_zero_injective
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L)) :
    Set.InjOn (fun d : Fin n → ons_Dart L ↦ d 0)
      (ons_decSquarefreeLoopFinset (n := n) L a b S :
        Set (Fin n → ons_Dart L)) := by
  intro d hd e he hzero
  change d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S at hd
  change e ∈ ons_decSquarefreeLoopFinset (n := n) L a b S at he
  rw [ons_mem_decSquarefreeLoopFinset] at hd he
  change d 0 = e 0 at hzero
  let hdvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let hevalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e he.2
  exact ons_squarefree_valid_loop_eq_of_zero_eq
    L d e hdvalid hevalid S hd.1 he.1 hzero

theorem ons_decLoop_portEdge_injective_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    Function.Injective (fun k : Fin n ↦ ons_portEdge L (d k)) := by
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hexponent
  have hnodup := ons_decWalkExternalDarts_portEdge_nodup q hq
  rw [ons_decLoopWalk_externalDarts L d hvalid] at hnodup
  rw [← List.ofFn_comp'] at hnodup
  have hinjGeom : Function.Injective
      (fun k : Fin n ↦ ons_portEdge L
        (ons_decGeometricLoopStates d k)) :=
    List.nodup_ofFn.mp hnodup
  intro i j hij
  have hgeom : ons_portEdge L
      (ons_decGeometricLoopStates d (-i)) =
      ons_portEdge L (ons_decGeometricLoopStates d (-j)) := by
    simpa [ons_decGeometricLoopStates] using hij
  have hneg : -i = -j := hinjGeom hgeom
  simpa using congrArg Neg.neg hneg

theorem ons_decLoop_dart_ne_rev_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (i j : Fin n) :
    d i ≠ ons_dartRev L (d j) := by
  intro hij
  have hedge : ons_portEdge L (d i) = ons_portEdge L (d j) := by
    rw [hij, ons_portEdge_rev]
  have hindex := ons_decLoop_portEdge_injective_of_squarefree
    L d hvalid S hexponent hedge
  subst j
  exact ons_dartRev_ne_self L (d i) hij.symm

noncomputable def ons_decLoopRootFinset
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    Finset (ons_Dart L) :=
  Finset.univ.image d ∪
    Finset.univ.image (fun k ↦ ons_dartRev L (d k))

theorem ons_decLoopRootFinset_card_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopRootFinset L d).card = 2 * n := by
  let f := fun k : Fin n ↦ ons_portEdge L (d k)
  have hfinj : Function.Injective f :=
    ons_decLoop_portEdge_injective_of_squarefree
      L d hvalid S hexponent
  have hdinj : Function.Injective d := by
    intro i j hij
    apply hfinj
    exact congrArg (ons_portEdge L) hij
  have hrevinj : Function.Injective
      (fun k : Fin n ↦ ons_dartRev L (d k)) := by
    intro i j hij
    apply hdinj
    have h := congrArg (ons_dartRev L) hij
    rw [ons_dartRev_involutive, ons_dartRev_involutive] at h
    exact h
  have hdisj : Disjoint (Finset.univ.image d)
      (Finset.univ.image (fun k ↦ ons_dartRev L (d k))) := by
    rw [Finset.disjoint_left]
    intro dart hdart hdartRev
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hdart
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hdartRev
    exact ons_decLoop_dart_ne_rev_of_squarefree
      L d hvalid S hexponent i j hj.symm
  unfold ons_decLoopRootFinset
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hdinj,
    Finset.card_image_of_injective _ hrevinj]
  simp
  omega

theorem ons_decSquarefreeLoop_root_edge_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    s(d 0, ons_dartRev L (d 0)) ∈ S := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hd.1
  have hedge : s(d 0, ons_dartRev L (d 0)) ∈ q.edges := by
    have hfirst := q.mk_start_snd_mem_edges hq.not_nil
    rw [ons_decLoopWalk_snd L d hvalid] at hfirst
    exact hfirst
  rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
    L d hvalid S hd.1]
  exact List.mem_toFinset.mpr hedge

theorem ons_external_root_mem_decLoopRootFinset
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (root : ons_Dart L)
    (hroot : s(root, ons_dartRev L root) ∈ S) :
    root ∈ ons_decLoopRootFinset L d := by
  classical
  let q := ons_decLoopWalk L d hvalid
  have hqedge : s(root, ons_dartRev L root) ∈ q.edges.toFinset := by
    rw [ons_decLoopWalk_edges_toFinset_of_squarefree
      L d hvalid S hexponent]
    exact hroot
  have hport : ons_portEdge L root ∈ ons_walkOriginalEdges q := by
    unfold ons_walkOriginalEdges ons_walkExternalEdges
      ons_decoratedExternalEdges
    rw [Finset.mem_image]
    refine ⟨s(root, ons_dartRev L root), ?_,
      ons_decEdgeProjection_external L root⟩
    exact Finset.mem_filter.mpr ⟨hqedge, ⟨root, rfl⟩⟩
  rw [← ons_decWalkExternalDarts_image_portEdge q,
    Finset.mem_image] at hport
  obtain ⟨dart, hdart, hprojection⟩ := hport
  rw [ons_decLoopWalk_externalDarts L d hvalid,
    List.mem_toFinset, List.mem_ofFn] at hdart
  obtain ⟨k, hk⟩ := hdart
  rcases (ons_portEdge_eq_iff L root dart).mp hprojection with heq | heq
  ·
    unfold ons_decLoopRootFinset
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    refine ⟨-k, Finset.mem_univ _, ?_⟩
    calc
      d (-k) = dart := by
        simpa [ons_decGeometricLoopStates] using hk
      _ = root := heq
  ·
    unfold ons_decLoopRootFinset
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨-k, Finset.mem_univ _, ?_⟩
    calc
      ons_dartRev L (d (-k)) = ons_dartRev L dart := by
        exact congrArg (ons_dartRev L)
          (by simpa [ons_decGeometricLoopStates] using hk)
      _ = root := by
        rw [heq, ons_dartRev_involutive]

def ons_decLoopOrientation
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    Fin n ⊕ Fin n → (Fin n → ons_Dart L)
  | Sum.inl k => ons_rotate k d
  | Sum.inr k => ons_rotate k (ons_loopRev L d)

theorem ons_decLoopOrientation_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
    (orientation : Fin n ⊕ Fin n) :
    ons_decLoopOrientation L d orientation ∈
      ons_decSquarefreeLoopFinset L a b S := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd ⊢
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  cases orientation with
  | inl k =>
      exact ⟨(ons_decLoopExponent_rotate L d k).trans hd.1,
        by simpa [ons_decLoopOrientation,
          ons_decLoopScalar_rotate] using hd.2⟩
  | inr k =>
      refine ⟨?_, ?_⟩
      · rw [ons_decLoopOrientation, ons_decLoopExponent_rotate,
          ons_decLoopExponent_loopRev L d hvalid, hd.1]
      · rw [ons_decLoopOrientation, ons_decLoopScalar_rotate,
          ons_decLoopScalar_loopRev_spin]
        exact hd.2

theorem ons_decLoopOrientation_injective
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    Function.Injective (ons_decLoopOrientation L d) := by
  have hport := ons_decLoop_portEdge_injective_of_squarefree
    L d hvalid S hexponent
  intro x y hxy
  have hzero := congrFun hxy 0
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have hij : i = j := by
            apply hport
            simpa [ons_decLoopOrientation, ons_rotate] using
              congrArg (ons_portEdge L) hzero
          subst j
          rfl
      | inr j =>
          exfalso
          have hbad : d i = ons_dartRev L (d (-j)) := by
            simpa [ons_decLoopOrientation, ons_rotate, ons_loopRev] using hzero
          exact ons_decLoop_dart_ne_rev_of_squarefree
            L d hvalid S hexponent i (-j) hbad
  | inr i =>
      cases y with
      | inl j =>
          exfalso
          have hbad : d j = ons_dartRev L (d (-i)) := by
            simpa [ons_decLoopOrientation, ons_rotate, ons_loopRev] using hzero.symm
          exact ons_decLoop_dart_ne_rev_of_squarefree
            L d hvalid S hexponent j (-i) hbad
      | inr j =>
          have hrev : d (-i) = d (-j) := by
            have h := congrArg (ons_dartRev L) hzero
            simp only [ons_decLoopOrientation, ons_rotate, ons_loopRev,
              zero_add] at h
            rw [ons_dartRev_involutive, ons_dartRev_involutive] at h
            exact h
          have hneg : -i = -j := by
            apply hport
            exact congrArg (ons_portEdge L) hrev
          have hij : i = j := by
            simpa using congrArg Neg.neg hneg
          subst j
          rfl

theorem ons_decSquarefreeLoopFinset_card_le
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
    (ons_decSquarefreeLoopFinset (n := n) L a b S).card ≤ 2 * n := by
  let loops := ons_decSquarefreeLoopFinset (n := n) L a b S
  let roots := loops.image (fun e ↦ e 0)
  have hcardRoots : roots.card = loops.card := by
    apply Finset.card_image_of_injOn
    exact ons_decSquarefreeLoop_eval_zero_injective L a b S
  rw [ons_mem_decSquarefreeLoopFinset] at hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  have hsubset : roots ⊆ ons_decLoopRootFinset L d := by
    intro root hroot
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hroot
    apply ons_external_root_mem_decLoopRootFinset
      L d hvalid S hd.1 (e 0)
    apply ons_decSquarefreeLoop_root_edge_mem L a b S
    exact he
  calc
    (ons_decSquarefreeLoopFinset (n := n) L a b S).card = roots.card := by
      exact hcardRoots.symm
    _ ≤ (ons_decLoopRootFinset L d).card :=
      Finset.card_le_card hsubset
    _ = 2 * n := ons_decLoopRootFinset_card_of_squarefree
      L d hvalid S hd.1

theorem ons_decSquarefreeLoopFinset_card_ge
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
    2 * n ≤ (ons_decSquarefreeLoopFinset (n := n) L a b S).card := by
  let loops := ons_decSquarefreeLoopFinset (n := n) L a b S
  let orient : Fin n ⊕ Fin n → {e // e ∈ loops} := fun k ↦
    ⟨ons_decLoopOrientation L d k,
      ons_decLoopOrientation_mem L a b S hd k⟩
  have hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d
    ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2
  have horient : Function.Injective orient := by
    intro i j hij
    apply ons_decLoopOrientation_injective L d hvalid S
      ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).1
    exact congrArg Subtype.val hij
  have hcard := Fintype.card_le_of_injective orient horient
  simpa [loops, Fintype.card_sum, two_mul] using hcard

theorem ons_decSquarefreeLoopFinset_card
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
    (ons_decSquarefreeLoopFinset (n := n) L a b S).card = 2 * n := by
  apply Nat.le_antisymm
  · exact ons_decSquarefreeLoopFinset_card_le L a b S hd
  · exact ons_decSquarefreeLoopFinset_card_ge L a b S hd

theorem ons_decLoopRootFinset_mem_external
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (root : ons_Dart L) :
    root ∈ ons_decLoopRootFinset L d ↔
      s(root, ons_dartRev L root) ∈ S := by
  constructor
  · intro hroot
    unfold ons_decLoopRootFinset at hroot
    rw [Finset.mem_union] at hroot
    rcases hroot with hroot | hroot
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hroot
      let q := ons_decLoopWalk L d hvalid
      have hmem : d k ∈ ons_decWalkExternalDarts q := by
        rw [ons_decLoopWalk_externalDarts L d hvalid, List.mem_ofFn]
        exact ⟨-k, by simp [ons_decGeometricLoopStates]⟩
      have hedge := ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts q hmem
      rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hvalid S hexponent]
      exact List.mem_toFinset.mpr hedge
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hroot
      rw [ons_dartRev_involutive, Sym2.eq_swap]
      let q := ons_decLoopWalk L d hvalid
      have hmem : d k ∈ ons_decWalkExternalDarts q := by
        rw [ons_decLoopWalk_externalDarts L d hvalid, List.mem_ofFn]
        exact ⟨-k, by simp [ons_decGeometricLoopStates]⟩
      have hedge := ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts q hmem
      rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hvalid S hexponent]
      exact List.mem_toFinset.mpr hedge
  · exact ons_external_root_mem_decLoopRootFinset
      L d hvalid S hexponent root

theorem ons_decSquarefreeLoop_length_unique
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n m : ℕ} [NeZero n] [NeZero m]
    (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L} {e : Fin m → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
    (he : e ∈ ons_decSquarefreeLoopFinset L a b S) :
    n = m := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd he
  let hdvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let hevalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e he.2
  have hroots : ons_decLoopRootFinset L d = ons_decLoopRootFinset L e := by
    ext root
    rw [ons_decLoopRootFinset_mem_external L d hdvalid S hd.1,
      ons_decLoopRootFinset_mem_external L e hevalid S he.1]
  have hcard := congrArg Finset.card hroots
  rw [ons_decLoopRootFinset_card_of_squarefree L d hdvalid S hd.1,
    ons_decLoopRootFinset_card_of_squarefree L e hevalid S he.1] at hcard
  omega

theorem ons_walkOriginalEdges_eq_of_edges_toFinset_eq
    {L : ℕ} [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u u)
    (q : (ons_decGraph L).Walk v v)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    ons_walkOriginalEdges p = ons_walkOriginalEdges q := by
  unfold ons_walkOriginalEdges ons_walkExternalEdges
  rw [hedges]

theorem ons_decSquarefreeLoop_scalar_eq
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n m : ℕ} [NeZero n] [NeZero m]
    (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L} {e : Fin m → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
    (he : e ∈ ons_decSquarefreeLoopFinset L a b S) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) e := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd he
  let hdvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let hevalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e he.2
  have horiginal :
      ons_walkOriginalEdges (ons_decLoopWalk L d hdvalid) =
        ons_walkOriginalEdges (ons_decLoopWalk L e hevalid) := by
    apply ons_walkOriginalEdges_eq_of_edges_toFinset_eq
    rw [ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hdvalid S hd.1,
      ons_decLoopWalk_edges_toFinset_of_squarefree
        L e hevalid S he.1]
  have hhomology :
      ons_evenHomology L
          (ons_walkOriginalEdges (ons_decLoopWalk L d hdvalid)) =
        ons_evenHomology L
          (ons_walkOriginalEdges (ons_decLoopWalk L e hevalid)) :=
    congrArg (ons_evenHomology L) horiginal
  have hdscalar := ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
    L a b d S hd.1 hd.2
  have hescalar := ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
    L a b e S he.1 he.2
  calc
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d =
        -((ons_spinCharacter a b
          (ons_evenHomology L
            (ons_walkOriginalEdges (ons_decLoopWalk L d hdvalid))) : ℂ)) := by
      simpa only [hdvalid] using hdscalar
    _ = -((ons_spinCharacter a b
          (ons_evenHomology L
            (ons_walkOriginalEdges (ons_decLoopWalk L e hevalid))) : ℂ)) := by
      rw [hhomology]
    _ = ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) e := by
      simpa only [hevalid] using hescalar.symm

theorem ons_decSquarefreeLoop_bucket_sum
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    (∑ e : Fin n → ons_Dart L,
      if ons_decLoopExponent L e = ons_finsetExponent S then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) e
      else 0) =
      (2 * n : ℂ) *
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) d := by
  classical
  let loops := ons_decSquarefreeLoopFinset (n := n) L a b S
  calc
    (∑ e : Fin n → ons_Dart L,
      if ons_decLoopExponent L e = ons_finsetExponent S then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) e
      else 0) =
        ∑ e ∈ loops,
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) e := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro e he
        simp only [loops, ons_decSquarefreeLoopFinset,
          Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact he.1
      · intro e heExp heNot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heExp
        by_contra hscalar
        apply heNot
        simp [loops, ons_decSquarefreeLoopFinset, heExp, hscalar]
    _ = ∑ _e ∈ loops,
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d := by
      apply Finset.sum_congr rfl
      intro e he
      exact ons_decSquarefreeLoop_scalar_eq L a b S he hd
    _ = (2 * n : ℂ) *
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d := by
      rw [Finset.sum_const, nsmul_eq_mul,
        ons_decSquarefreeLoopFinset_card L a b S hd]
      norm_cast

theorem ons_decFormalLogCoeff_squarefree_of_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L)) (r : ℕ)
    (d : Fin (r + 1) → ons_Dart L)
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) =
      (ons_spinCharacter a b
        (ons_evenHomology L
          (ons_walkOriginalEdges
            (ons_decLoopWalk L d
              (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b) d
                ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
  have hddata := (ons_mem_decSquarefreeLoopFinset L a b S d).mp hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hddata.2
  change ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_finsetExponent S) =
    (ons_spinCharacter a b
      (ons_evenHomology L
        (ons_walkOriginalEdges (ons_decLoopWalk L d hvalid))) : ℂ)
  have hlength := ons_decLoopExponent_length_le L d
  rw [hddata.1] at hlength
  have hrange : r ∈ Finset.range
      (ons_finsuppTotalDegree (ons_finsetExponent S)) := by
    rw [Finset.mem_range]
    omega
  unfold ons_decFormalLogCoeff
  rw [Finset.sum_eq_single r]
  · rw [ons_decSquarefreeLoop_bucket_sum L a b S hd]
    have hscalar := ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
      L a b d S hddata.1 hddata.2
    have hscalar' :
        ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d =
          -((ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d hvalid))) : ℂ)) := by
      simpa only [hvalid] using hscalar
    calc
      (-(2 * ((r + 1 : ℕ) : ℂ) *
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) d /
            ((r : ℂ) + 1))) / 2 =
          -ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d := by
        push_cast
        field_simp
      _ = -(-((ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d hvalid))) : ℂ))) :=
        congrArg Neg.neg hscalar'
      _ = (ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d hvalid))) : ℂ) := by ring
  · intro r' hr' hne
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro e he
    by_cases hexp : ons_decLoopExponent L e = ons_finsetExponent S
    · by_cases hscalar : ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) e = 0
      · simp [hexp, hscalar]
      · exfalso
        have heMem : e ∈ ons_decSquarefreeLoopFinset L a b S :=
          (ons_mem_decSquarefreeLoopFinset L a b S e).mpr
            ⟨hexp, hscalar⟩
        have hlen := ons_decSquarefreeLoop_length_unique
          L a b S hd heMem
        omega
    · simp [hexp]
  · intro hnot
    exact (hnot hrange).elim

theorem ons_decFormalLogCoeff_squarefree_eq_zero_of_empty
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hempty : ∀ r : ℕ,
      (ons_decSquarefreeLoopFinset (n := r + 1) L a b S).Nonempty → False) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) = 0 := by
  unfold ons_decFormalLogCoeff
  suffices hsum : ∀ r : ℕ,
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = ons_finsetExponent S then
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d
        else 0) = 0 by
    simp [hsum]
  intro r
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hexp : ons_decLoopExponent L d = ons_finsetExponent S
  · by_cases hscalar : ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d = 0
    · simp [hexp, hscalar]
    · exfalso
      apply hempty r
      refine ⟨d, ?_⟩
      exact (ons_mem_decSquarefreeLoopFinset L a b S d).mpr
        ⟨hexp, hscalar⟩
  · simp [hexp]

theorem ons_decFormalLogCoeff_squarefree_cases
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L)) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) = 0 ∨
      ∃ (r : ℕ) (d : Fin (r + 1) → ons_Dart L)
        (hd : d ∈ ons_decSquarefreeLoopFinset L a b S),
        ons_decFormalLogCoeff L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)
            (ons_finsetExponent S) =
          (ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d
                  (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                    (ons_spinPhase L a) (ons_spinPhase L b) d
                    ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
  classical
  by_cases hexists : ∃ r : ℕ,
      (ons_decSquarefreeLoopFinset (n := r + 1) L a b S).Nonempty
  · right
    obtain ⟨r, d, hd⟩ := hexists
    exact ⟨r, d, hd,
      ons_decFormalLogCoeff_squarefree_of_mem L a b S r d hd⟩
  · left
    apply ons_decFormalLogCoeff_squarefree_eq_zero_of_empty L a b S
    intro r hr
    exact hexists ⟨r, hr⟩

theorem ons_decSquarefreeLoop_edges_even
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    S ∈ StatMech.Ising.evenSubgraphs (ons_decGraph L) := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hd.1
  rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
    L d hvalid S hd.1]
  exact ons_cycle_edges_evenSubgraph (ons_decGraph L) q hq

end StatMech.Onsager
