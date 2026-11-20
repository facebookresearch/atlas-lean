/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareBox










open SimpleGraph Set

namespace StatMech.Universality

noncomputable section





theorem walkCycleArcSplice_of_order
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {u v a b c d : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hab : p.support.idxOf a < p.support.idxOf b)
    (r : (G.deleteEdges {s(a, b), s(c, d)}).Walk d c)
    (hr : r.IsPath) (hd : d ∈ r.support) (hc : c ∈ r.support)
    (hdisjoint : p.support.Disjoint r.support) :
    ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v,
      q.IsPath ∧
        q.support =
          p.support.take (p.support.idxOf a + 1) ++
            r.support ++ p.support.drop (p.support.idxOf b) := by
  let cut : Set (Sym2 V) := {s(a, b), s(c, d)}
  let K := G.deleteEdges cut
  let H := medialTwoEdgeSwitch G a b c d
  let pa := p.takeUntil a ha
  let pb := p.dropUntil b hb
  have hpaSupport : pa.support =
      p.support.take (p.support.idxOf a + 1) := by
    simp [pa, Walk.takeUntil_eq_take,
      Walk.take_support_eq_support_take_succ]
  have hibLe : p.support.idxOf b ≤ p.length := by
    have hibLt := List.idxOf_lt_length_of_mem hb
    simpa [Walk.length_support] using hibLt
  have hpbSupport : pb.support =
      p.support.drop (p.support.idxOf b) := by
    simp [pb, Walk.dropUntil_eq_drop,
      Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hibLe]
  have hpaAvoid : ∀ e, e ∈ pa.edges → e ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · have hbpa := pa.snd_mem_support_of_mem_edges hf
      rw [hpaSupport, List.mem_take_iff_idxOf_lt hb] at hbpa
      omega
    · have hcpa : c ∈ p.support := by
        apply (List.take_sublist _ _).subset
        rw [← hpaSupport]
        exact pa.fst_mem_support_of_mem_edges hf
      exact hdisjoint hcpa hc
  have hsplitNodup :
      (p.support.take (p.support.idxOf b) ++
        p.support.drop (p.support.idxOf b)).Nodup := by
    simpa only [List.take_append_drop] using hp.support_nodup
  have hsplitDisjoint : List.Disjoint
      (p.support.take (p.support.idxOf b))
      (p.support.drop (p.support.idxOf b)) :=
    hsplitNodup.disjoint
  have haTake : a ∈ p.support.take (p.support.idxOf b) := by
    rw [List.mem_take_iff_idxOf_lt ha]
    exact hab
  have hpbAvoid : ∀ e, e ∈ pb.edges → e ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · exact hsplitDisjoint haTake
        (hpbSupport ▸ pb.fst_mem_support_of_mem_edges hf)
    · have hcpb : c ∈ p.support := by
        apply (List.drop_sublist _ _).subset
        rw [← hpbSupport]
        exact pb.fst_mem_support_of_mem_edges hf
      exact hdisjoint hcpb hc
  have hKle : K ≤ H := by
    intro x y hxy
    exact Or.inl (Or.inl hxy)
  have hadNe : a ≠ d := by
    intro had
    subst d
    exact hdisjoint ha hd
  have hcbNe : c ≠ b := by
    intro hcb
    subst c
    exact hdisjoint hb hc
  have had : H.Adj a d := by
    exact Or.inl (Or.inr (by
      simpa [SimpleGraph.edge_adj] using hadNe))
  have hcb : H.Adj c b := by
    exact Or.inr (by
      simpa [SimpleGraph.edge_adj] using hcbNe)
  let paK : K.Walk u a := pa.toDeleteEdges cut hpaAvoid
  let pbK : K.Walk b v := pb.toDeleteEdges cut hpbAvoid
  let paH := paK.mapLe hKle
  let rH := r.mapLe hKle
  let pbH := pbK.mapLe hKle
  let q := paH.append ((rH.cons had).append (pbH.cons hcb))
  have hpaHSupport : paH.support = pa.support := by
    simp only [paH, Walk.support_mapLe_eq_support]
    dsimp only [paK]
    apply Walk.support_transfer
  have hrHSupport : rH.support = r.support := by
    simp only [rH, Walk.support_mapLe_eq_support]
  have hpbHSupport : pbH.support = pb.support := by
    simp only [pbH, Walk.support_mapLe_eq_support]
    dsimp only [pbK]
    apply Walk.support_transfer
  have hqSupport : q.support =
      p.support.take (p.support.idxOf a + 1) ++
        r.support ++ p.support.drop (p.support.idxOf b) := by
    simp [q, Walk.support_append, hpaHSupport, hrHSupport, hpbHSupport,
      hpaSupport, hpbSupport]
  have haiLe : p.support.idxOf a + 1 ≤ p.support.idxOf b := by
    omega
  have houterSublist :
      (p.support.take (p.support.idxOf a + 1) ++
        p.support.drop (p.support.idxOf b)).Sublist p.support := by
    simpa [List.dropSlice_eq, Nat.add_sub_of_le haiLe] using
      List.dropSlice_sublist (p.support.idxOf a + 1)
        (p.support.idxOf b - (p.support.idxOf a + 1)) p.support
  have houterNodup :
      (p.support.take (p.support.idxOf a + 1) ++
        p.support.drop (p.support.idxOf b)).Nodup :=
    List.Nodup.sublist houterSublist hp.support_nodup
  have hparts := List.nodup_append.mp houterNodup
  have hprefixR : List.Disjoint
      (p.support.take (p.support.idxOf a + 1)) r.support := by
    rw [List.disjoint_left]
    intro x hx hxr
    exact hdisjoint ((List.take_sublist _ _).subset hx) hxr
  have hrSuffix : List.Disjoint r.support
      (p.support.drop (p.support.idxOf b)) := by
    rw [List.disjoint_left]
    intro x hxr hxs
    exact hdisjoint ((List.drop_sublist _ _).subset hxs) hxr
  have hprefixSuffix : List.Disjoint
      (p.support.take (p.support.idxOf a + 1))
      (p.support.drop (p.support.idxOf b)) := by
    rw [List.disjoint_left]
    intro x hxp hxs
    exact hparts.2.2 x hxp x hxs rfl
  have hprefixRNodup :
      (p.support.take (p.support.idxOf a + 1) ++ r.support).Nodup :=
    hparts.1.append hr.support_nodup hprefixR
  have hprefixRSuffix : List.Disjoint
      (p.support.take (p.support.idxOf a + 1) ++ r.support)
      (p.support.drop (p.support.idxOf b)) := by
    rw [List.disjoint_append_left]
    exact ⟨hprefixSuffix, hrSuffix⟩
  refine ⟨q, ?_, hqSupport⟩
  rw [Walk.isPath_def, hqSupport]
  exact hprefixRNodup.append hparts.2.1 hprefixRSuffix

end

end StatMech.Universality
