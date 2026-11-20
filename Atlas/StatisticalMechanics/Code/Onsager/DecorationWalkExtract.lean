/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationCycles









namespace StatMech.Onsager

def ons_decDartIsExternal {L : ℕ} (a : (ons_decGraph L).Dart) : Bool :=
  decide (a.snd = ons_dartRev L a.fst)

def ons_decWalkExternalDarts {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : List (ons_Dart L) :=
  (p.darts.filter ons_decDartIsExternal).map (fun a => a.fst)

theorem ons_decWalkExternalDarts_cons_external
    {L : ℕ} {u v w : ons_Dart L}
    (h : (ons_decGraph L).Adj u v) (p : (ons_decGraph L).Walk v w)
    (hrev : v = ons_dartRev L u) :
    ons_decWalkExternalDarts (SimpleGraph.Walk.cons h p) =
      u :: ons_decWalkExternalDarts p := by
  subst v
  simp [ons_decWalkExternalDarts, ons_decDartIsExternal]



theorem ons_decWalkExternalDarts_head
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    (ons_decWalkExternalDarts q).head? = some d := by
  have hqnil : ¬ q.Nil := hq.not_nil
  rw [← q.cons_tail_eq hqnil]
  rw [ons_decWalkExternalDarts_cons_external]
  · rfl
  · simpa using hsnd



theorem ons_decWalkExternalDarts_nodup
    {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    (ons_decWalkExternalDarts q).Nodup := by
  have hsupport : q.support.dropLast.Nodup := by
    have hrev := ((SimpleGraph.Walk.isCycle_def q.reverse).mp hq.reverse).2.2
    simpa [SimpleGraph.Walk.support_reverse] using hrev
  have hdarts :
      (q.darts.map (fun a : (ons_decGraph L).Dart => a.fst)).Nodup := by
    rw [q.map_fst_darts]
    exact hsupport
  have hsub : List.Sublist (ons_decWalkExternalDarts q)
      (q.darts.map (fun a : (ons_decGraph L).Dart => a.fst)) := by
    change List.Sublist
      ((q.darts.filter ons_decDartIsExternal).map
        (fun a : (ons_decGraph L).Dart => a.fst))
      (q.darts.map (fun a : (ons_decGraph L).Dart => a.fst))
    exact (List.filter_sublist.map
      (fun a : (ons_decGraph L).Dart => a.fst))
  exact hdarts.sublist hsub



theorem ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {d : ons_Dart L}
    (hd : d ∈ ons_decWalkExternalDarts p) :
    s(d, ons_dartRev L d) ∈ p.edges := by
  rw [ons_decWalkExternalDarts, List.mem_map] at hd
  obtain ⟨a, ha, rfl⟩ := hd
  have hdata := List.mem_filter.mp ha
  have haext : a.snd = ons_dartRev L a.fst := by
    simpa [ons_decDartIsExternal] using hdata.2
  rw [SimpleGraph.Walk.edges, List.mem_map]
  refine ⟨a, hdata.1, ?_⟩
  apply Sym2.eq_iff.mpr
  exact Or.inl ⟨rfl, haext⟩



theorem ons_decWalkExternalDarts_image_portEdge
    {L : ℕ} [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decWalkExternalDarts p).toFinset.image (ons_portEdge L) =
      ons_walkOriginalEdges p := by
  classical
  ext edge
  constructor
  · rw [Finset.mem_image]
    rintro ⟨d, hd, rfl⟩
    rw [ons_walkOriginalEdges, Finset.mem_image]
    refine ⟨s(d, ons_dartRev L d), ?_,
      ons_decEdgeProjection_external L d⟩
    rw [ons_walkExternalEdges, ons_decoratedExternalEdges,
      Finset.mem_filter]
    exact ⟨List.mem_toFinset.mpr
      (ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts p
        (List.mem_toFinset.mp hd)), ⟨d, rfl⟩⟩
  · rw [ons_walkOriginalEdges, Finset.mem_image]
    rintro ⟨decEdge, hdecEdge, rfl⟩
    rw [ons_walkExternalEdges, ons_decoratedExternalEdges,
      Finset.mem_filter] at hdecEdge
    rcases hdecEdge.2 with ⟨d, rfl⟩
    have hedge : s(d, ons_dartRev L d) ∈ p.edges :=
      List.mem_toFinset.mp hdecEdge.1
    rw [SimpleGraph.Walk.edges, List.mem_map] at hedge
    obtain ⟨a, ha, haedge⟩ := hedge
    change s(a.fst, a.snd) = s(d, ons_dartRev L d) at haedge
    rw [Sym2.eq_iff] at haedge
    rcases haedge with haedge | haedge
    · have haext : ons_decDartIsExternal a = true := by
        simp [ons_decDartIsExternal, haedge.1, haedge.2]
      have hamem : a.fst ∈ ons_decWalkExternalDarts p := by
        rw [ons_decWalkExternalDarts, List.mem_map]
        exact ⟨a, List.mem_filter.mpr ⟨ha, haext⟩, rfl⟩
      rw [Finset.mem_image]
      refine ⟨a.fst, List.mem_toFinset.mpr hamem, ?_⟩
      rw [haedge.1, ons_decEdgeProjection_external]
    · have haext : ons_decDartIsExternal a = true := by
        have hrel : a.snd = ons_dartRev L a.fst := by
          rw [haedge.1, haedge.2]
          exact (ons_dartRev_involutive L d).symm
        simp [ons_decDartIsExternal, hrel]
      have hamem : a.fst ∈ ons_decWalkExternalDarts p := by
        rw [ons_decWalkExternalDarts, List.mem_map]
        exact ⟨a, List.mem_filter.mpr ⟨ha, haext⟩, rfl⟩
      rw [Finset.mem_image]
      refine ⟨a.fst, List.mem_toFinset.mpr hamem, ?_⟩
      rw [haedge.1, ons_portEdge_rev,
        ons_decEdgeProjection_external]



theorem ons_decWalkExternalEdges_nodup
    {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    ((ons_decWalkExternalDarts q).map
      (fun e => s(e, ons_dartRev L e))).Nodup := by
  have heq :
      (ons_decWalkExternalDarts q).map
          (fun e => s(e, ons_dartRev L e)) =
        (q.darts.filter ons_decDartIsExternal).map
          SimpleGraph.Dart.edge := by
    rw [ons_decWalkExternalDarts, List.map_map]
    apply List.map_congr_left
    intro a ha
    have haext : a.snd = ons_dartRev L a.fst := by
      simpa [ons_decDartIsExternal] using (List.mem_filter.mp ha).2
    change s(a.fst, ons_dartRev L a.fst) = s(a.fst, a.snd)
    rw [haext]
  rw [heq]
  have hsub : List.Sublist
      ((q.darts.filter ons_decDartIsExternal).map
        SimpleGraph.Dart.edge) q.edges := by
    rw [SimpleGraph.Walk.edges]
    exact List.filter_sublist.map SimpleGraph.Dart.edge
  exact hq.edges_nodup.sublist hsub



theorem ons_decWalkExternalDarts_portEdge_nodup
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    ((ons_decWalkExternalDarts q).map (ons_portEdge L)).Nodup := by
  exact (ons_decWalkExternalDarts_nodup q hq).map_on (by
    intro e he f hf hef
    rcases (ons_portEdge_eq_iff L f e).mp hef with h | h
    · exact h
    · have hinj := List.inj_on_of_nodup_map
          (ons_decWalkExternalEdges_nodup q hq)
      apply hinj he hf
      rw [h, ons_dartRev_involutive]
      exact Sym2.eq_swap)



theorem ons_walkOriginalEdges_prod_eq_externalDarts
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) :
    ∏ edge ∈ ons_walkOriginalEdges q, weight edge =
      ((ons_decWalkExternalDarts q).map
        (fun e => weight (ons_portEdge L e))).prod := by
  classical
  rw [← ons_decWalkExternalDarts_image_portEdge q]
  have hinj : Set.InjOn (ons_portEdge L)
      ((ons_decWalkExternalDarts q).toFinset : Set (ons_Dart L)) := by
    intro e he f hf hef
    exact List.inj_on_of_nodup_map
      (ons_decWalkExternalDarts_portEdge_nodup q hq)
      (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf) hef
  rw [Finset.prod_image hinj]
  exact List.prod_toFinset _ (ons_decWalkExternalDarts_nodup q hq)




def ons_decCycleFirstReturn {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) : List (ons_Dart L) :=
  d :: (ons_decWalkExternalDarts q).tail.reverse ++ [d]

theorem ons_decCycleFirstReturn_isFirstReturn
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_isFirstReturnSegment d (ons_decCycleFirstReturn q) := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hnodup : ext.Nodup := ons_decWalkExternalDarts_nodup q hq
  have hdnot : d ∉ ext.tail := by
    rw [hext, List.nodup_cons] at hnodup
    exact hnodup.1
  refine ⟨ext.tail.reverse, rfl, ?_⟩
  intro e he hed
  subst e
  exact hdnot (by simpa using he)

theorem ons_decCycleFirstReturn_avoids_reverse
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∀ e ∈ ons_decCycleFirstReturn q, e ≠ ons_dartRev L d := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hdmem : d ∈ ext := by rw [hext]; simp
  have hrevnot : ons_dartRev L d ∉ ext := by
    intro hrev
    have hinj := List.inj_on_of_nodup_map
      (ons_decWalkExternalDarts_portEdge_nodup q hq)
    have heq : d = ons_dartRev L d :=
      hinj hdmem hrev (ons_portEdge_rev L d).symm
    exact (ons_dartRev_ne_self L d) heq.symm
  have hrevnotTail : ons_dartRev L d ∉ ext.tail := by
    intro hrev
    exact hrevnot (by rw [hext]; simp [hrev])
  intro e he
  change e ∈
    (d :: (ons_decWalkExternalDarts q).tail.reverse) ++ [d] at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_cons.mp he with hed | he
    · subst e
      exact (ons_dartRev_ne_self L d).symm
    · intro hed
      rw [hed] at he
      exact hrevnotTail (by simpa [ext] using he)
  · have hed : e = d := by simpa using he
    subst e
    exact (ons_dartRev_ne_self L d).symm

theorem ons_decCycleFirstReturn_valid
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_isFirstReturnSegment d (ons_decCycleFirstReturn q) ∧
      ∀ e ∈ ons_decCycleFirstReturn q, e ≠ ons_dartRev L d :=
  ⟨ons_decCycleFirstReturn_isFirstReturn q hq hsnd,
    ons_decCycleFirstReturn_avoids_reverse q hq hsnd⟩

end StatMech.Onsager
