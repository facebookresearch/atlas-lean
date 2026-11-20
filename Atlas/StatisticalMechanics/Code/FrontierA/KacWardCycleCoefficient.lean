/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardUnitCycleReduction











open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager

universe u


noncomputable def kwGraphSquarefreeLoopFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V)) :
    Finset (Fin n → G.Dart) :=
  Finset.univ.filter fun loop ↦
    kwGraphLoopExponent G loop = ons_finsetExponent S ∧
      kwGraphLoopScalar G phase loop ≠ 0

theorem kwGraph_mem_squarefreeLoopFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    (loop : Fin n → G.Dart) :
    loop ∈ kwGraphSquarefreeLoopFinset G phase S ↔
      kwGraphLoopExponent G loop = ons_finsetExponent S ∧
        kwGraphLoopScalar G phase loop ≠ 0 := by
  simp [kwGraphSquarefreeLoopFinset]



theorem kwGraphLoopWalk_snd
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ∀ k, G.DartAdj (loop k) (loop (k + 1))) :
    (kwGraphLoopWalk G loop hvalid).snd = (loop 0).snd := by
  have hdarts := kwGraphLoopWalk_darts G loop hvalid
  have hne : ¬(kwGraphLoopWalk G loop hvalid).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rw [← SimpleGraph.Walk.length_darts, hdarts, List.length_ofFn]
    exact NeZero.pos n
  have hpos : 0 < (kwGraphLoopWalk G loop hvalid).darts.length := by
    rw [hdarts, List.length_ofFn]
    exact NeZero.pos n
  have hfirst := SimpleGraph.Walk.firstDart_eq hne hpos
  have hfirst' : (kwGraphLoopWalk G loop hvalid).firstDart hne = loop 0 := by
    simpa only [kwGraphLoopWalk_darts, List.getElem_ofFn] using hfirst
  simpa using congrArg (fun dart : G.Dart ↦ dart.snd) hfirst'



theorem kwGraph_squarefreeLoop_eval_zero_injective
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V)) :
    Set.InjOn (fun loop : Fin n → G.Dart ↦ loop 0)
      (kwGraphSquarefreeLoopFinset (n := n) G phase S :
        Set (Fin n → G.Dart)) := by
  intro d hd e he hzero
  change d ∈ kwGraphSquarefreeLoopFinset G phase S at hd
  change e ∈ kwGraphSquarefreeLoopFinset G phase S at he
  rw [kwGraph_mem_squarefreeLoopFinset] at hd he
  let hdvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase d hd.2
  let hevalid := kwGraphLoop_valid_of_scalar_ne_zero G phase e he.2
  let pd := kwGraphLoopWalk G d hdvalid
  let pe := kwGraphLoopWalk G e hevalid
  have hdtrail := kwGraphLoopWalk_isTrail_and_edges G d hdvalid S hd.1
  have hetrail := kwGraphLoopWalk_isTrail_and_edges G e hevalid S he.1
  have hpdne : pd ≠ .nil := by
    intro hnil
    have hlen := congrArg List.length (kwGraphLoopWalk_darts G d hdvalid)
    rw [show kwGraphLoopWalk G d hdvalid = pd from rfl, hnil] at hlen
    simp at hlen
    exact (NeZero.ne n) hlen.symm
  have hpene : pe ≠ .nil := by
    intro hnil
    have hlen := congrArg List.length (kwGraphLoopWalk_darts G e hevalid)
    rw [show kwGraphLoopWalk G e hevalid = pe from rfl, hnil] at hlen
    simp at hlen
    exact (NeZero.ne n) hlen.symm
  have hpd : pd.IsCycle :=
    kw_closedTrail_isCycle_of_degree_le_three G pd hdtrail.1 hpdne hdeg
  have hpe : pe.IsCycle :=
    kw_closedTrail_isCycle_of_degree_le_three G pe hetrail.1 hpene hdeg
  let pe' : G.Walk (d 0).fst (d 0).fst := pe.copy
    (congrArg (fun dart : G.Dart ↦ dart.fst) hzero).symm
    (congrArg (fun dart : G.Dart ↦ dart.fst) hzero).symm
  have hpe' : pe'.IsCycle := by
    exact (SimpleGraph.Walk.isCycle_copy pe
      (congrArg (fun dart : G.Dart ↦ dart.fst) hzero).symm).mpr hpe
  have hsnd : pd.snd = pe'.snd := by
    rw [kwGraphLoopWalk_snd G d hdvalid]
    change (d 0).snd = (pe.copy _ _).snd
    change (d 0).snd = (pe.copy _ _).getVert 1
    rw [SimpleGraph.Walk.getVert_copy]
    change (d 0).snd = pe.snd
    rw [kwGraphLoopWalk_snd G e hevalid]
    exact congrArg (fun dart : G.Dart ↦ dart.snd) hzero
  have hedges : pd.edges.toFinset = pe'.edges.toFinset := by
    rw [show pd.edges.toFinset = S from hdtrail.2,
      SimpleGraph.Walk.edges_copy]
    exact hetrail.2.symm
  have hpde : pd = pe' :=
    ons_rooted_isCycle_eq_of_snd_edges_eq pd pe' hpd hpe' hsnd hedges
  apply List.ofFn_injective
  rw [← kwGraphLoopWalk_darts G d hdvalid,
    ← kwGraphLoopWalk_darts G e hevalid]
  simpa [pd, pe, pe'] using congrArg SimpleGraph.Walk.darts hpde

theorem kwGraphLoopExponent_rotate
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) (r : Fin n) :
    kwGraphLoopExponent G (ons_rotate r loop) =
      kwGraphLoopExponent G loop := by
  unfold kwGraphLoopExponent
  simpa [ons_rotate, add_comm, add_left_comm, add_assoc] using
    Equiv.sum_comp (Equiv.addRight r)
      (fun k : Fin n ↦ Finsupp.single (loop k).edge 1)

theorem kwGraphLoopScalar_rotate
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) (r : Fin n) :
    kwGraphLoopScalar G phase (ons_rotate r loop) =
      kwGraphLoopScalar G phase loop := by
  exact ons_loopWeight_rotate
    (kwGraphTransition G (fun _ ↦ 1) phase) r loop


def kwGraphLoopRev
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : Fin n → G.Dart :=
  ons_involutiveLoopRev SimpleGraph.Dart.symm loop

@[simp] theorem kwGraphLoopRev_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) (k : Fin n) :
    kwGraphLoopRev loop k = (loop (-k)).symm := rfl

theorem kwGraphLoopExponent_loopRev
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopExponent G (kwGraphLoopRev loop) =
      kwGraphLoopExponent G loop := by
  unfold kwGraphLoopExponent kwGraphLoopRev ons_involutiveLoopRev
  simp only [SimpleGraph.Dart.edge_symm]
  exact Equiv.sum_comp (Equiv.neg (Fin n))
    (fun k : Fin n ↦ Finsupp.single (loop k).edge 1)


theorem kwGraphLoopScalar_loopRev_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G embedding.turnPhase (kwGraphLoopRev loop) =
      kwGraphLoopScalar G embedding.turnPhase loop := by
  exact kwStraightLineGraphLoopWeight_loopRev G embedding (fun _ ↦ 1) loop


noncomputable def kwGraphLoopRootFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : Finset G.Dart :=
  Finset.univ.image loop ∪
    Finset.univ.image (fun k ↦ (loop k).symm)

theorem kwGraphLoopRootFinset_card_of_squarefree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    (kwGraphLoopRootFinset loop).card = 2 * n := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have htrail := kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1
  have hedgeNodup :
      ((List.ofFn loop).map SimpleGraph.Dart.edge).Nodup := by
    rw [← kwGraphLoopWalk_edges G loop hvalid]
    exact htrail.1.edges_nodup
  rw [← List.ofFn_comp'] at hedgeNodup
  have hedgeInj : Function.Injective
      (fun k : Fin n ↦ (loop k).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  have hloopInj : Function.Injective loop := by
    intro i j hij
    exact hedgeInj (congrArg (fun dart : G.Dart ↦ dart.edge) hij)
  have hrevInj : Function.Injective (fun k ↦ (loop k).symm) := by
    intro i j hij
    apply hloopInj
    simpa using congrArg SimpleGraph.Dart.symm hij
  have hdisj : Disjoint (Finset.univ.image loop)
      (Finset.univ.image (fun k ↦ (loop k).symm)) := by
    rw [Finset.disjoint_left]
    intro dart hdart hdartRev
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hdart
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hdartRev
    have hij : i = j := by
      apply hedgeInj
      calc
        (loop i).edge = ((loop j).symm).edge :=
          congrArg (fun dart : G.Dart ↦ dart.edge) hj.symm
        _ = (loop j).edge := SimpleGraph.Dart.edge_symm _
    subst j
    exact (loop i).symm_ne hj
  unfold kwGraphLoopRootFinset
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hloopInj,
    Finset.card_image_of_injective _ hrevInj]
  simp
  omega

theorem kwGraph_squarefreeLoop_root_edge_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    (loop 0).edge ∈ S := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have hedges := (kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1).2
  rw [← hedges, kwGraphLoopWalk_edges]
  simp

theorem kwGraph_root_mem_loopRootFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S)
    (root : G.Dart) (hroot : root.edge ∈ S) :
    root ∈ kwGraphLoopRootFinset loop := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have hedges := (kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1).2
  rw [← hedges, kwGraphLoopWalk_edges, List.mem_toFinset,
    List.mem_map] at hroot
  obtain ⟨dart, hdart, hedge⟩ := hroot
  rw [List.mem_ofFn] at hdart
  obtain ⟨k, rfl⟩ := hdart
  rcases (SimpleGraph.dart_edge_eq_iff root (loop k)).mp hedge.symm with heq | heq
  · subst root
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩)
  · subst root
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩)


def kwGraphLoopOrientation
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    Fin n ⊕ Fin n → (Fin n → G.Dart)
  | Sum.inl k => ons_rotate k loop
  | Sum.inr k => ons_rotate k (kwGraphLoopRev loop)

theorem kwGraphLoopOrientation_mem_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (orientation : Fin n ⊕ Fin n) :
    kwGraphLoopOrientation loop orientation ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase S := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop ⊢
  cases orientation with
  | inl k =>
      exact ⟨(kwGraphLoopExponent_rotate G loop k).trans hloop.1,
        by simpa [kwGraphLoopOrientation, kwGraphLoopScalar_rotate]
          using hloop.2⟩
  | inr k =>
      refine ⟨?_, ?_⟩
      · rw [kwGraphLoopOrientation, kwGraphLoopExponent_rotate,
          kwGraphLoopExponent_loopRev, hloop.1]
      · rw [kwGraphLoopOrientation, kwGraphLoopScalar_rotate,
          kwGraphLoopScalar_loopRev_straightLine]
        exact hloop.2

theorem kwGraphLoopOrientation_injective_of_squarefree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    Function.Injective (kwGraphLoopOrientation loop) := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have htrail := kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1
  have hedgeNodup :
      ((List.ofFn loop).map SimpleGraph.Dart.edge).Nodup := by
    rw [← kwGraphLoopWalk_edges G loop hvalid]
    exact htrail.1.edges_nodup
  rw [← List.ofFn_comp'] at hedgeNodup
  have hedgeInj : Function.Injective
      (fun k : Fin n ↦ (loop k).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  intro x y hxy
  have hzero := congrFun hxy 0
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          exact congrArg Sum.inl (hedgeInj
            (congrArg (fun dart : G.Dart ↦ dart.edge)
              (by simpa [kwGraphLoopOrientation, ons_rotate] using hzero)))
      | inr j =>
          exfalso
          have hbad : loop i = (loop (-j)).symm := by
            simpa [kwGraphLoopOrientation, ons_rotate,
              kwGraphLoopRev, ons_involutiveLoopRev] using hzero
          have hij : i = -j := by
            apply hedgeInj
            calc
              (loop i).edge = ((loop (-j)).symm).edge :=
                congrArg (fun dart : G.Dart ↦ dart.edge) hbad
              _ = (loop (-j)).edge := SimpleGraph.Dart.edge_symm _
          have hself : loop i = (loop i).symm :=
            hbad.trans (congrArg SimpleGraph.Dart.symm
              (congrArg loop hij.symm))
          exact (loop i).symm_ne hself.symm
  | inr i =>
      cases y with
      | inl j =>
          exfalso
          have hbad : loop j = (loop (-i)).symm := by
            simpa [kwGraphLoopOrientation, ons_rotate,
              kwGraphLoopRev, ons_involutiveLoopRev] using hzero.symm
          have hji : j = -i := by
            apply hedgeInj
            calc
              (loop j).edge = ((loop (-i)).symm).edge :=
                congrArg (fun dart : G.Dart ↦ dart.edge) hbad
              _ = (loop (-i)).edge := SimpleGraph.Dart.edge_symm _
          have hself : loop j = (loop j).symm :=
            hbad.trans (congrArg SimpleGraph.Dart.symm
              (congrArg loop hji.symm))
          exact (loop j).symm_ne hself.symm
      | inr j =>
          have hrev : loop (-i) = loop (-j) := by
            have := congrArg SimpleGraph.Dart.symm hzero
            simpa [kwGraphLoopOrientation, ons_rotate,
              kwGraphLoopRev, ons_involutiveLoopRev] using this
          have hneg : -i = -j :=
            hedgeInj (congrArg (fun dart : G.Dart ↦ dart.edge) hrev)
          exact congrArg Sum.inr (by
            simpa using congrArg Neg.neg hneg)

theorem kwGraphSquarefreeLoopFinset_card_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    (kwGraphSquarefreeLoopFinset (n := n)
      G embedding.turnPhase S).card = 2 * n := by
  let loops := kwGraphSquarefreeLoopFinset (n := n)
    G embedding.turnPhase S
  let roots := loops.image (fun e ↦ e 0)
  have hcardRoots : roots.card = loops.card := by
    apply Finset.card_image_of_injOn
    exact kwGraph_squarefreeLoop_eval_zero_injective
      G embedding.turnPhase hdeg S
  have hsubset : roots ⊆ kwGraphLoopRootFinset loop := by
    intro root hroot
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hroot
    apply kwGraph_root_mem_loopRootFinset
      G embedding.turnPhase S hloop (e 0)
    exact kwGraph_squarefreeLoop_root_edge_mem
      G embedding.turnPhase S he
  have hle : loops.card ≤ 2 * n := by
    calc
      loops.card = roots.card := hcardRoots.symm
      _ ≤ (kwGraphLoopRootFinset loop).card := Finset.card_le_card hsubset
      _ = 2 * n := kwGraphLoopRootFinset_card_of_squarefree
        G embedding.turnPhase S hloop
  have hge : 2 * n ≤ loops.card := by
    let orient : Fin n ⊕ Fin n → {e // e ∈ loops} := fun k ↦
      ⟨kwGraphLoopOrientation loop k,
        kwGraphLoopOrientation_mem_straightLine
          G embedding S hloop k⟩
    have horient : Function.Injective orient := by
      intro i j hij
      apply kwGraphLoopOrientation_injective_of_squarefree
        G embedding.turnPhase S hloop
      exact congrArg Subtype.val hij
    have hcard := Fintype.card_le_of_injective orient horient
    simpa [loops, Fintype.card_sum, two_mul] using hcard
  exact Nat.le_antisymm hle hge

theorem kwGraphSquarefreeLoop_scalar_eq_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {d e : Fin n → G.Dart}
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (he : e ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    kwGraphLoopScalar G embedding.turnPhase e =
      kwGraphLoopScalar G embedding.turnPhase d := by
  have hrootEdge := kwGraph_squarefreeLoop_root_edge_mem
    G embedding.turnPhase S he
  have hroot := kwGraph_root_mem_loopRootFinset
    G embedding.turnPhase S hd (e 0) hrootEdge
  unfold kwGraphLoopRootFinset at hroot
  rw [Finset.mem_union] at hroot
  have hinj := kwGraph_squarefreeLoop_eval_zero_injective (n := n)
    G embedding.turnPhase hdeg S
  rcases hroot with hroot | hroot
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hroot
    have hrot := kwGraphLoopOrientation_mem_straightLine
      G embedding S hd (Sum.inl k)
    have heq : e = ons_rotate k d := by
      apply hinj he hrot
      simpa [kwGraphLoopOrientation, ons_rotate] using hk.symm
    rw [heq, kwGraphLoopScalar_rotate]
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hroot
    have hrot := kwGraphLoopOrientation_mem_straightLine
      G embedding S hd (Sum.inr (-k))
    have heq : e = ons_rotate (-k) (kwGraphLoopRev d) := by
      apply hinj he hrot
      simpa [kwGraphLoopOrientation, ons_rotate,
        kwGraphLoopRev, ons_involutiveLoopRev] using hk.symm
    rw [heq, kwGraphLoopScalar_rotate,
      kwGraphLoopScalar_loopRev_straightLine]

theorem kwGraphSquarefreeLoop_bucket_sum_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {d : Fin n → G.Dart}
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    (∑ e : Fin n → G.Dart,
      if kwGraphLoopExponent G e = ons_finsetExponent S then
        kwGraphLoopScalar G embedding.turnPhase e else 0) =
      (2 * n : ℂ) * kwGraphLoopScalar G embedding.turnPhase d := by
  classical
  let loops := kwGraphSquarefreeLoopFinset (n := n)
    G embedding.turnPhase S
  calc
    (∑ e : Fin n → G.Dart,
      if kwGraphLoopExponent G e = ons_finsetExponent S then
        kwGraphLoopScalar G embedding.turnPhase e else 0) =
        ∑ e ∈ loops, kwGraphLoopScalar G embedding.turnPhase e := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro e he
        simp only [loops, kwGraphSquarefreeLoopFinset,
          Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact he.1
      · intro e heExp heNot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heExp
        by_contra hscalar
        apply heNot
        simp [loops, kwGraphSquarefreeLoopFinset, heExp, hscalar]
    _ = ∑ _e ∈ loops, kwGraphLoopScalar G embedding.turnPhase d := by
      apply Finset.sum_congr rfl
      intro e he
      exact kwGraphSquarefreeLoop_scalar_eq_straightLine
        G embedding hdeg S hd he
    _ = (2 * n : ℂ) * kwGraphLoopScalar G embedding.turnPhase d := by
      rw [Finset.sum_const, nsmul_eq_mul,
        kwGraphSquarefreeLoopFinset_card_straightLine
          G embedding hdeg S hd]
      norm_cast




theorem kwGraphFormalLogCoeff_squarefree_of_mem_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (r : ℕ)
    (d : Fin (r + 1) → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent S) =
      -kwGraphLoopScalar G embedding.turnPhase d := by
  have hddata := (kwGraph_mem_squarefreeLoopFinset
    G embedding.turnPhase S d).mp hd
  have hdegree : ons_finsuppTotalDegree (ons_finsetExponent S) = r + 1 := by
    rw [← hddata.1]
    exact kwGraphLoopExponent_totalDegree G d
  have hrange : r ∈ Finset.range
      (ons_finsuppTotalDegree (ons_finsetExponent S)) := by
    rw [Finset.mem_range, hdegree]
    omega
  unfold kwGraphFormalLogCoeff
  rw [Finset.sum_eq_single r]
  · rw [kwGraphSquarefreeLoop_bucket_sum_straightLine
      G embedding hdeg S hd]
    push_cast
    field_simp
  · intro r' hr' hne
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro e he
    by_cases hexp : kwGraphLoopExponent G e = ons_finsetExponent S
    · exfalso
      have hdegree' := kwGraphLoopExponent_totalDegree G e
      rw [hexp, hdegree] at hdegree'
      omega
    · simp [hexp]
  · intro hnot
    exact (hnot hrange).elim

theorem kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (r : ℕ)
    (d : Fin (r + 1) → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (hscalar : kwGraphLoopScalar G embedding.turnPhase d = -1) :
    kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent S) = 1 := by
  rw [kwGraphFormalLogCoeff_squarefree_of_mem_straightLine
    G embedding hdeg S r d hd, hscalar]
  ring

theorem kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one'
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) {n : ℕ} [NeZero n]
    (d : Fin n → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (hscalar : kwGraphLoopScalar G embedding.turnPhase d = -1) :
    kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent S) = 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one
    G embedding hdeg S r d hd hscalar




noncomputable def kwGraphCycleDartLoop
    {V : Type u} {G : SimpleGraph V} {root : V}
    (p : G.Walk root root) : Fin p.darts.length → G.Dart :=
  p.darts.get

@[simp] theorem kwGraphCycleDartLoop_ofFn
    {V : Type u} {G : SimpleGraph V} {root : V}
    (p : G.Walk root root) :
    List.ofFn (kwGraphCycleDartLoop p) = p.darts := by
  exact List.ofFn_get p.darts

theorem kwGraphCycleDartLoop_valid
    {V : Type u} {G : SimpleGraph V} {root : V}
    (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∀ k, G.DartAdj (kwGraphCycleDartLoop p k)
      (kwGraphCycleDartLoop p (k + 1)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  unfold kwGraphCycleDartLoop SimpleGraph.DartAdj
  change (p.darts[k.1]'k.2).snd =
    (p.darts[(k + 1).1]'(k + 1).2).fst
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert,
    SimpleGraph.Walk.darts_getElem_eq_getVert]
  change p.getVert (k.1 + 1) = p.getVert (k + 1).1
  by_cases hwrap : k.1 + 1 = p.darts.length
  · have hval : (k + 1).1 = 0 := by
      rw [Fin.val_add]
      have hlen : 3 ≤ p.darts.length := by
        simpa [SimpleGraph.Walk.length_darts] using hp.three_le_length
      simp [hwrap]
    rw [hval, hwrap, SimpleGraph.Walk.length_darts]
    simp
  · have hlt : k.1 + 1 < p.darts.length := by omega
    rw [Fin.val_add_one_of_lt' hlt]

theorem kwGraphCycleDartLoop_exponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwGraphLoopExponent G (kwGraphCycleDartLoop p) =
      ons_finsetExponent p.edges.toFinset := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let hvalid := kwGraphCycleDartLoop_valid p hp
  calc
    kwGraphLoopExponent G (kwGraphCycleDartLoop p) =
        Multiset.toFinsupp
          ((kwGraphLoopWalk G (kwGraphCycleDartLoop p) hvalid).edges :
            Multiset (Sym2 V)) :=
      (kwGraphLoopWalk_edgeCount G (kwGraphCycleDartLoop p) hvalid).symm
    _ = Multiset.toFinsupp (p.edges : Multiset (Sym2 V)) := by
      congr 2
      rw [kwGraphLoopWalk_edges, kwGraphCycleDartLoop_ofFn,
        ← SimpleGraph.Walk.edges]
    _ = ons_finsetExponent p.edges.toFinset :=
      (ons_finsetExponent_toFinset_eq_edgeCount
        p.edges hp.edges_nodup).symm

theorem kwGraphCycleDartLoop_nonbacktracking
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwGraphLoopNonbacktracking G (kwGraphCycleDartLoop p) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  refine ⟨kwGraphCycleDartLoop_valid p hp k, ?_⟩
  have hedgeNodup :
      (List.ofFn (fun i : Fin p.darts.length ↦
        (kwGraphCycleDartLoop p i).edge)).Nodup := by
    rw [List.ofFn_comp', kwGraphCycleDartLoop_ofFn]
    simpa [SimpleGraph.Walk.edges] using hp.edges_nodup
  have hedgeInj : Function.Injective
      (fun i : Fin p.darts.length ↦
        (kwGraphCycleDartLoop p i).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  intro hedge
  have hindex : k = k + 1 := hedgeInj hedge
  have hzeroOne : (0 : Fin p.darts.length) = 1 := by
    apply add_left_cancel (a := k)
    simpa using hindex
  have hval := congrArg Fin.val hzeroOne
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hdartsLen : p.darts.length = p.length := p.length_darts
  simp at hval
  omega

theorem kwGraphCycleDartLoop_scalar_eq_phaseProduct
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwGraphLoopScalar G phase (kwGraphCycleDartLoop p) =
      kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [kwGraphLoopScalar_eq_adjacency_mul_phaseProduct]
  have hadj : kwGraphLoopAdjacency G (kwGraphCycleDartLoop p) = 1 := by
    unfold kwGraphLoopAdjacency
    apply Finset.prod_eq_one
    intro k hk
    rw [if_pos (kwGraphCycleDartLoop_nonbacktracking G p hp k)]
  rw [hadj, one_mul]




theorem kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      kwLoopPhaseProduct embedding.turnPhase
        (kwGraphCycleDartLoop p) = -1) :
    kwGraphFormalLogCoeff G embedding.turnPhase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hscalar : kwGraphLoopScalar G embedding.turnPhase
      (kwGraphCycleDartLoop p) = -1 := by
    rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct G
      embedding.turnPhase p hp]
    exact hphase
  have hd : kwGraphCycleDartLoop p ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase
        p.edges.toFinset := by
    rw [kwGraph_mem_squarefreeLoopFinset]
    exact ⟨kwGraphCycleDartLoop_exponent G p hp, by
      rw [hscalar]
      norm_num⟩
  exact kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one'
    G embedding hdeg p.edges.toFinset (kwGraphCycleDartLoop p) hd hscalar

end StatMech.FrontierA
