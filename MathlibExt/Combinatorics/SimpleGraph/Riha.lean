/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Říha's cycle lemma

This file proves that a prescribed vertex of a finite 2-vertex-connected graph lies on a cycle
with another vertex having no neighbors outside that cycle.
-/

@[expose] public section

namespace SimpleGraph

private theorem List.exists_split_first {α : Type*} (P : α → Prop) {l : List α}
    (h : ∃ a ∈ l, P a) :
    ∃ pre a post, l = pre ++ a :: post ∧ P a ∧ ∀ z ∈ pre, ¬P z := by
  classical
  induction l with
  | nil => simp at h
  | cons a l ih =>
      by_cases ha : P a
      · exact ⟨[], a, l, rfl, ha, by simp⟩
      · have htail : ∃ b ∈ l, P b := by
          obtain ⟨b, hb, hPb⟩ := h
          exact ⟨b, (List.mem_cons.mp hb).resolve_left fun hba ↦ ha (hba ▸ hPb), hPb⟩
        obtain ⟨pre, b, post, hsplit, hPb, hpre⟩ := ih htail
        refine ⟨a :: pre, b, post, by simp [hsplit], hPb, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ha
        · exact hpre z hz

private theorem List.exists_split_consecutive {α : Type*} (P : α → Prop) {l : List α}
    (h : ∃ a ∈ l, ∃ b ∈ l, a ≠ b ∧ P a ∧ P b) :
    ∃ pre a mid b post,
      l = pre ++ a :: mid ++ b :: post ∧ P a ∧ P b ∧ ∀ z ∈ mid, ¬P z := by
  classical
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀, hPa₀, hPb₀⟩ := h
  obtain ⟨pre, a, rest, hsplit, hPa, hpre⟩ :=
    List.exists_split_first P ⟨a₀, ha₀, hPa₀⟩
  have hrest : ∃ b ∈ rest, P b := by
    have mem_rest_of_mem_ne {z : α} (hz : z ∈ l) (hPz : P z) (hza : z ≠ a) :
        z ∈ rest := by
      rw [hsplit, List.mem_append, List.mem_cons] at hz
      rcases hz with hz | hza' | hz
      · exact False.elim (hpre z hz hPz)
      · exact False.elim (hza hza')
      · exact hz
    by_cases hba : b₀ = a
    · have haa : a₀ ≠ a := fun h ↦ hab₀ (h.trans hba.symm)
      exact ⟨a₀, mem_rest_of_mem_ne ha₀ hPa₀ haa, hPa₀⟩
    · exact ⟨b₀, mem_rest_of_mem_ne hb₀ hPb₀ hba, hPb₀⟩
  obtain ⟨mid, b, post, hsplit', hPb, hmid⟩ := List.exists_split_first P hrest
  refine ⟨pre, a, mid, b, post, ?_, hPa, hPb, hmid⟩
  rw [hsplit, hsplit']
  simp

private theorem List.take_idxOf_add_one_of_eq_append_cons {α : Type*} [DecidableEq α]
    {l pre post : List α} {a : α} (hl : l = pre ++ a :: post) (ha : a ∉ pre) :
    l.take (l.idxOf a + 1) = pre ++ [a] := by
  subst l
  rw [List.idxOf_append_of_notMem ha]
  rw [List.take_append]
  simp

private theorem List.drop_idxOf_of_eq_append_cons {α : Type*} [DecidableEq α]
    {l pre post : List α} {a : α} (hl : l = pre ++ a :: post) (ha : a ∉ pre) :
    l.drop (l.idxOf a) = a :: post := by
  subst l
  rw [List.idxOf_append_of_notMem ha]
  rw [List.drop_append]
  simp

private theorem List.not_mem_suffix_of_nodup_split {α : Type*}
    {pre mid post : List α} {a b : α} (h : (pre ++ a :: mid ++ b :: post).Nodup) :
    a ∉ mid ++ b :: post := by
  have heq : pre ++ a :: mid ++ b :: post =
      (pre ++ [a]) ++ (mid ++ b :: post) := by
    simp [List.append_assoc]
  rw [heq] at h
  exact List.disjoint_left.mp h.disjoint (by simp)

private theorem List.first_ne_getLast_of_nodup_split {α : Type*}
    {pre mid post : List α} {a b : α} (h : (pre ++ a :: mid ++ b :: post).Nodup) :
    a ≠ (pre ++ a :: mid ++ b :: post).getLast (by simp) := by
  intro ha
  apply List.not_mem_suffix_of_nodup_split h
  rw [ha]
  have hlast := List.getLast_mem (l := mid ++ b :: post) (by simp)
  simp at hlast ⊢

private def Walk.outside {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) : Set V :=
  {v | v ∉ c.support}

private def Walk.componentVerts {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) : Set V :=
  Subtype.val '' K.supp

private theorem Walk.componentVerts_nonempty {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) :
    (c.componentVerts K).Nonempty := by
  obtain ⟨v, hv⟩ := K.nonempty_supp
  exact ⟨v, v, hv, rfl⟩

private theorem Walk.componentVerts_subset_outside {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) :
    c.componentVerts K ⊆ c.outside := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

private theorem Walk.exists_isPath_componentVerts
    {V : Type*} {G : SimpleGraph V} {x d e : V} (c : G.Walk x x)
    (K : (G.induce c.outside).ConnectedComponent) (hd : d ∈ c.componentVerts K)
    (he : e ∈ c.componentVerts K) :
    ∃ p : G.Walk d e, p.IsPath ∧ ∀ z ∈ p.support, z ∈ c.componentVerts K := by
  obtain ⟨d', hdK, rfl⟩ := hd
  obtain ⟨e', heK, rfl⟩ := he
  obtain ⟨p, hp⟩ := K.connected_toSimpleGraph.exists_isPath
    ⟨d', hdK⟩ ⟨e', heK⟩
  let f := (Embedding.induce c.outside).toHom.comp K.toSimpleGraph_hom
  let q : G.Walk (d' : V) (e' : V) := p.map f
  refine ⟨q, hp.map ?_, ?_⟩
  · intro u v huv
    exact Subtype.ext (Subtype.ext huv)
  · intro z hz
    change z ∈ (p.map f).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact ⟨z'.val, z'.property, rfl⟩

private theorem Walk.mem_componentVerts_of_adj {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) {v w : V}
    (hv : v ∈ c.componentVerts K) (hvw : G.Adj v w) (hw : w ∈ c.outside) :
    w ∈ c.componentVerts K := by
  obtain ⟨v', hv', rfl⟩ := hv
  let w' : c.outside := ⟨w, hw⟩
  have hadj : (G.induce c.outside).Adj v' w' := hvw
  exact ⟨w', K.mem_supp_of_adj_mem_supp hv' hadj, rfl⟩

/-- **Bound vertices of a closed walk.** Let $c$ be a closed walk in a simple graph $G$. A vertex
$y$ is bound to $c$ when $y$ lies on $c$ and every neighbor of $y$ in $G$ lies on $c$. -/
public def Walk.IsBoundVertex {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (y : V) : Prop :=
  y ∈ c.support ∧ ∀ ⦃z⦄, G.Adj y z → z ∈ c.support

/-- **Characterization of bound vertices.** Let $c$ be a closed walk in a simple graph $G$. A
vertex $y$ is bound to $c$ if and only if $y$ lies on $c$ and every neighbor of $y$ in $G$ lies
on $c$. -/
public theorem Walk.isBoundVertex_iff {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (y : V) :
    c.IsBoundVertex y ↔ y ∈ c.support ∧ ∀ ⦃z⦄, G.Adj y z → z ∈ c.support :=
  Iff.rfl

private theorem Walk.IsCycle.exists_boundVertex_of_outside_eq_empty
    {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    (hout : c.outside = ∅) : ∃ y, y ≠ x ∧ c.IsBoundVertex y := by
  have hall : ∀ z, z ∈ c.support := by
    intro z
    by_contra hz
    have : z ∈ c.outside := hz
    rw [hout] at this
    exact this
  refine ⟨c.snd, (c.adj_snd hc.not_nil).ne.symm, ?_, ?_⟩
  · exact List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil)
  · intro z _
    exact hall z

private def rihaCandidate {V : Type*} (G : SimpleGraph V) (x : V) (n : ℕ) : Prop :=
  ∃ (c : G.Walk x x) (_hc : c.IsCycle)
    (K : (G.induce c.outside).ConnectedComponent), (c.componentVerts K).ncard = n

private def Walk.IsAttachment {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) (v : V) : Prop :=
  v ∈ c.support ∧ ∃ d ∈ c.componentVerts K, G.Adj v d

private theorem Walk.mem_componentVerts_of_adj_of_unique_attachment
    {V : Type*} {G : SimpleGraph V} {x a v w : V} (c : G.Walk x x)
    (K : (G.induce c.outside).ConnectedComponent)
    (hunique : ∀ b, c.IsAttachment K b → b = a) (hv : v ∈ c.componentVerts K)
    (hvw : G.Adj v w) (hwa : w ≠ a) : w ∈ c.componentVerts K := by
  by_cases hw : w ∈ c.support
  · have hatt : c.IsAttachment K w := ⟨hw, v, hv, hvw.symm⟩
    exact False.elim (hwa (hunique w hatt))
  · exact c.mem_componentVerts_of_adj K hv hvw hw

private theorem Walk.end_mem_componentVerts_of_unique_attachment
    {V : Type*} {G : SimpleGraph V} {x a : V} (c : G.Walk x x)
    (K : (G.induce c.outside).ConnectedComponent)
    (hunique : ∀ b, c.IsAttachment K b → b = a)
    {d t : {v : V // v ∈ (↑({a} : Finset V) : Set V)ᶜ}}
    (p : (G.induce (↑({a} : Finset V) : Set V)ᶜ).Walk d t)
    (hd : (d : V) ∈ c.componentVerts K) : (t : V) ∈ c.componentVerts K := by
  induction p with
  | nil => exact hd
  | @cons _ z _ h p ih =>
      have hza : (z : V) ≠ a := by simpa using z.property
      exact ih (c.mem_componentVerts_of_adj_of_unique_attachment K hunique hd
        (induce_adj.mp h) hza)

private theorem Walk.mem_componentVerts_of_adj_of_no_attachment
    {V : Type*} {G : SimpleGraph V} {x v w : V} (c : G.Walk x x)
    (K : (G.induce c.outside).ConnectedComponent)
    (hno : ∀ b, ¬c.IsAttachment K b) (hv : v ∈ c.componentVerts K)
    (hvw : G.Adj v w) : w ∈ c.componentVerts K := by
  by_cases hw : w ∈ c.support
  · exact False.elim (hno w ⟨hw, v, hv, hvw.symm⟩)
  · exact c.mem_componentVerts_of_adj K hv hvw hw

private theorem Walk.end_mem_componentVerts_of_no_attachment
    {V : Type*} {G : SimpleGraph V} {x d t : V} (c : G.Walk x x)
    (K : (G.induce c.outside).ConnectedComponent)
    (hno : ∀ b, ¬c.IsAttachment K b) (p : G.Walk d t)
    (hd : d ∈ c.componentVerts K) : t ∈ c.componentVerts K := by
  induction p with
  | nil => exact hd
  | @cons _ z _ h p ih =>
      exact ih (c.mem_componentVerts_of_adj_of_no_attachment K hno hd h)

private theorem Connected.exists_cycle_attachment
    {V : Type*} {G : SimpleGraph V} {x : V} (hG : G.Connected) (c : G.Walk x x)
    (K : (G.induce c.outside).ConnectedComponent) : ∃ a, c.IsAttachment K a := by
  obtain ⟨d, hd⟩ := c.componentVerts_nonempty K
  by_contra! hno
  obtain ⟨p⟩ := hG d x
  have hx := c.end_mem_componentVerts_of_no_attachment K hno p hd
  exact (c.componentVerts_subset_outside K hx) c.start_mem_support

private theorem Walk.IsCycle.exists_mem_support_ne
    {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    (a : V) : ∃ t ∈ c.support, t ≠ a := by
  by_cases hax : a = x
  · refine ⟨c.snd, List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil), ?_⟩
    exact hax ▸ (c.adj_snd hc.not_nil).ne.symm
  · exact ⟨x, c.start_mem_support, Ne.symm hax⟩

private theorem IsVertexConnected.exists_two_cycle_attachments
    {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.IsVertexConnected 2)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    (K : (G.induce c.outside).ConnectedComponent) :
    ∃ a, c.IsAttachment K a ∧ ∃ b, c.IsAttachment K b ∧ b ≠ a := by
  classical
  obtain ⟨a, ha⟩ := (hG.connected (by omega)).exists_cycle_attachment c K
  refine ⟨a, ha, ?_⟩
  by_contra! hunique
  obtain ⟨t, ht, hta⟩ := hc.exists_mem_support_ne a
  obtain ⟨d, hd⟩ := c.componentVerts_nonempty K
  have hda : d ≠ a := by
    intro h
    exact (c.componentVerts_subset_outside K hd) (h ▸ ha.1)
  let d' : {v : V // v ∈ (↑({a} : Finset V) : Set V)ᶜ} := ⟨d, by simpa⟩
  let t' : {v : V // v ∈ (↑({a} : Finset V) : Set V)ᶜ} := ⟨t, by simpa⟩
  obtain ⟨p⟩ := (hG.connected_compl_singleton (by omega) a) d' t'
  have htD := c.end_mem_componentVerts_of_unique_attachment K hunique p hd
  exact (c.componentVerts_subset_outside K htD) ht

private theorem Walk.IsCycle.exists_consecutive_arc
    {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    (P : V → Prop)
    (htwo : ∃ a ∈ c.support, ∃ b ∈ c.support, a ≠ b ∧ P a ∧ P b) :
    ∃ (a b : V) (p : G.Walk a b) (q : G.Walk b a),
      a ≠ b ∧ P a ∧ P b ∧ p.IsPath ∧ q.IsPath ∧
        (p.append q).IsCycle ∧ x ∈ q.support ∧
        (∀ z ∈ p.support, z ≠ a → z ≠ b → ¬P z) ∧
        (∀ z ∈ q.support, z ∈ c.support) ∧
        ∀ z ∈ c.support, z ∈ p.support ∨ z ∈ q.support := by
  classical
  have htail_of_support {z : V} (hz : z ∈ c.support) : z ∈ c.tail.support := by
    rw [← c.cons_support_tail hc.not_nil] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact c.tail.end_mem_support
    · exact hz
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀, hPa₀, hPb₀⟩ := htwo
  obtain ⟨pre, a, mid, b, post, hsplit, hPa, hPb, hmid⟩ :=
    List.exists_split_consecutive P
      ⟨a₀, htail_of_support ha₀, b₀, htail_of_support hb₀, hab₀, hPa₀, hPb₀⟩
  have htpath := hc.isPath_tail
  have hnodup : (pre ++ a :: mid ++ b :: post).Nodup := by
    rw [← hsplit]
    exact htpath.support_nodup
  have hab : a ≠ b := by
    intro hab
    exact List.not_mem_suffix_of_nodup_split hnodup (by simp [hab])
  have hax : a ≠ x := by
    have htlast : c.tail.support.getLast? = some x := by
      rw [List.getLast?_eq_some_getLast c.tail.support_ne_nil,
        c.tail.getLast_support]
    have hlast? : (pre ++ a :: mid ++ b :: post).getLast? = some x :=
      (congrArg List.getLast? hsplit).symm.trans htlast
    have hlast : (pre ++ a :: mid ++ b :: post).getLast (by simp) = x := by
      rw [List.getLast?_eq_some_getLast (by simp)] at hlast?
      exact Option.some.inj hlast?
    intro hax
    exact List.first_ne_getLast_of_nodup_split hnodup (hax.trans hlast.symm)
  have ha : a ∈ c.tail.support := by
    rw [hsplit]
    simp
  let u := c.tail.takeUntil a ha
  let r := c.tail.dropUntil a ha
  have hapre : a ∉ pre := by
    intro ha'
    have heq : pre ++ a :: mid ++ b :: post =
        pre ++ (a :: (mid ++ b :: post)) := by simp [List.append_assoc]
    have hn := hnodup
    rw [heq, List.nodup_append] at hn
    have hd := hn.2.2 a ha' a (by simp)
    exact hd rfl
  have haidx : c.tail.support.idxOf a ≤ c.tail.length := by
    have := List.idxOf_lt_length_of_mem ha
    rw [c.tail.length_support] at this
    omega
  have husupport : u.support = pre ++ [a] := by
    simp only [u, Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take]
    apply List.take_idxOf_add_one_of_eq_append_cons
      (post := mid ++ b :: post) (ha := hapre)
    simpa [List.append_assoc] using hsplit
  have hrsupport : r.support = a :: mid ++ b :: post := by
    simp only [r, Walk.dropUntil_eq_drop, Walk.support_copy,
      Walk.drop_support_eq_support_drop_min, Nat.min_eq_left haidx]
    apply List.drop_idxOf_of_eq_append_cons
      (post := mid ++ b :: post) (ha := hapre)
    simpa [List.append_assoc] using hsplit
  have hb : b ∈ r.support := by
    rw [hrsupport]
    simp
  let p := r.takeUntil b hb
  let v := r.dropUntil b hb
  have hbprefix : b ∉ a :: mid := by
    intro hb'
    rcases List.mem_cons.mp hb' with hba | hbmid
    · exact hab hba.symm
    · exact hmid b hbmid hPb
  have hbidx : r.support.idxOf b ≤ r.length := by
    have := List.idxOf_lt_length_of_mem hb
    rw [r.length_support] at this
    omega
  have hpsupport : p.support = (a :: mid) ++ [b] := by
    simp only [p, Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take]
    exact List.take_idxOf_add_one_of_eq_append_cons hrsupport hbprefix
  have hvsupport : v.support = b :: post := by
    simp only [v, Walk.dropUntil_eq_drop, Walk.support_copy,
      Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hbidx]
    exact List.drop_idxOf_of_eq_append_cons hrsupport hbprefix
  have hupath : u.IsPath := htpath.takeUntil ha
  have hrpath : r.IsPath := htpath.dropUntil ha
  have hppath : p.IsPath := hrpath.takeUntil hb
  have hvpath : v.IsPath := hrpath.dropUntil hb
  have hxnotu : x ∉ u.support := by
    exact Walk.endpoint_notMem_support_takeUntil htpath ha (Ne.symm hax)
  let s : G.Walk x a := Walk.cons (c.adj_snd hc.not_nil) u
  have hspath : s.IsPath := hupath.cons hxnotu
  let q : G.Walk b a := v.append s
  have hqpath : q.IsPath := by
    change (v.append s).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    refine ⟨hvpath.support_nodup, ?_, ?_⟩
    · simpa [s] using hspath.support_nodup.tail
    · intro z hzv z' hzs hzz'
      subst z'
      simp only [s, Walk.support_cons, List.tail_cons] at hzs
      rw [hvsupport] at hzv
      rw [husupport] at hzs
      have heq : pre ++ a :: mid ++ b :: post =
          (pre ++ [a]) ++ (mid ++ b :: post) := by
        simp [List.append_assoc]
      have hn := hnodup
      rw [heq] at hn
      have hnot := List.disjoint_left.mp hn.disjoint hzs
      exact hnot (by simp only [List.mem_append, List.mem_cons] at hzv ⊢; aesop)
  have hac : a ∈ c.support := by
    rw [← c.cons_support_tail hc.not_nil]
    exact List.mem_cons_of_mem x ha
  have htake : c.takeUntil a hac = s := by
    have ht := Walk.takeUntil_cons (p := c.tail) ha (Ne.symm hax)
      (c.adj_snd hc.not_nil)
    simpa only [c.cons_tail_eq hc.not_nil, u, s] using ht
  have hdrop : c.dropUntil a hac = r := by
    have hd :
        (Walk.cons (c.adj_snd hc.not_nil) c.tail).dropUntil a
            (List.mem_of_mem_tail ha) = c.tail.dropUntil a ha := by
      simp [Walk.dropUntil, Ne.symm hax]
    simpa only [c.cons_tail_eq hc.not_nil, r] using hd
  have hpv : p.append v = r := r.take_spec hb
  have hpqrotate : p.append q = c.rotate a hac := by
    simp only [q, Walk.append_assoc, hpv, Walk.rotate, hdrop, htake]
  have hpqcycle : (p.append q).IsCycle := by
    rw [hpqrotate]
    exact hc.rotate hac
  have hxq : x ∈ q.support := by
    change x ∈ (v.append s).support
    rw [Walk.mem_support_append_iff]
    exact Or.inl v.end_mem_support
  refine ⟨a, b, p, q, hab, hPa, hPb, hppath, hqpath, hpqcycle, hxq, ?_, ?_, ?_⟩
  · intro z hz hza hzb
    rw [hpsupport, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | hzb'
    · rcases List.mem_cons.mp hz with hza' | hz
      · exact False.elim (hza hza')
      · exact hmid z hz
    · exact False.elim (hzb hzb')
  · intro z hz
    change z ∈ (v.append s).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hzv | hzs
    · rw [hvsupport] at hzv
      rw [← c.cons_support_tail hc.not_nil]
      apply List.mem_cons_of_mem
      rw [hsplit]
      simp only [List.mem_append, List.mem_cons] at hzv ⊢
      aesop
    · simp only [s, Walk.support_cons, List.mem_cons] at hzs
      rcases hzs with rfl | hzu
      · exact c.start_mem_support
      · rw [husupport] at hzu
        rw [← c.cons_support_tail hc.not_nil]
        apply List.mem_cons_of_mem
        rw [hsplit]
        simp only [List.mem_append, List.mem_cons] at hzu ⊢
        aesop
  · intro z hzc
    have hzrotate : z ∈ (c.rotate a hac).support :=
      (Walk.mem_support_rotate_iff c a hac).mpr hzc
    rw [← hpqrotate, Walk.mem_support_append_iff] at hzrotate
    exact hzrotate

private theorem IsVertexConnected.exists_bound_or_smaller_component
    {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.IsVertexConnected 2)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    (K : (G.induce c.outside).ConnectedComponent) :
    ∃ (c' : G.Walk x x) (_hc' : c'.IsCycle) (y : V), y ∈ c'.support ∧ y ≠ x ∧
        (c'.IsBoundVertex y ∨
          ∃ L : (G.induce c'.outside).ConnectedComponent,
            c'.componentVerts L ⊂ c.componentVerts K) := by
  classical
  have htwo := hG.exists_two_cycle_attachments hc K
  have htwo' :
      ∃ a ∈ c.support, ∃ b ∈ c.support,
        a ≠ b ∧ c.IsAttachment K a ∧ c.IsAttachment K b := by
    obtain ⟨a, ha, b, hb, hba⟩ := htwo
    exact ⟨a, ha.1, b, hb.1, Ne.symm hba, ha, hb⟩
  obtain ⟨a, b, p, q, hab, ha, hb, hp, hq, hpq, hxq, hno, hqsub, hcover⟩ :=
    hc.exists_consecutive_arc (fun z ↦ c.IsAttachment K z) htwo'
  obtain ⟨d, hdK, had⟩ := ha.2
  obtain ⟨e, heK, hbe⟩ := hb.2
  obtain ⟨r, hr, hrK⟩ := c.exists_isPath_componentVerts K hdK heK
  have hadnot : a ∉ r.support := by
    intro har
    exact (c.componentVerts_subset_outside K (hrK a har)) ha.1
  have hbenot : b ∉ r.support := by
    intro hbr
    exact (c.componentVerts_subset_outside K (hrK b hbr)) hb.1
  let s : G.Walk a e := Walk.cons had r
  have hs : s.IsPath := hr.cons hadnot
  have hbnot : b ∉ s.support := by
    intro hbs
    simp only [s, Walk.support_cons, List.mem_cons] at hbs
    rcases hbs with hba | hbr
    · exact hab hba.symm
    · exact hbenot hbr
  let dpath : G.Walk a b := s.concat hbe.symm
  have hdpath : dpath.IsPath := hs.concat hbnot hbe.symm
  have hdpath_length : 1 < dpath.length := by
    simp only [dpath, s, Walk.length_concat, Walk.length_cons]
    omega
  have hbnotq : b ∉ q.support.tail := by
    have hn := hq.support_nodup
    rw [← q.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hdisjoint : dpath.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro z hzd hzq
    have hzd' : z ∈ r.support ∨ z = b := by
      have hsupp : dpath.support.tail = r.support ++ [b] := by
        simp [dpath, s]
      rw [hsupp, List.mem_append, List.mem_singleton] at hzd
      exact hzd
    rcases hzd' with hzr | rfl
    · have hzK := hrK z hzr
      have hzc := hqsub z (List.mem_of_mem_tail hzq)
      exact (c.componentVerts_subset_outside K hzK) hzc
    · exact hbnotq hzq
  let c₁ : G.Walk a a := dpath.append q
  have hc₁ : c₁.IsCycle := hdpath.isCycle_append hq hdisjoint (Or.inl hdpath_length)
  have hxc₁ : x ∈ c₁.support := by
    change x ∈ (dpath.append q).support
    rw [Walk.mem_support_append_iff]
    exact Or.inr hxq
  have hdc₁ : d ∈ c₁.support := by
    change d ∈ (dpath.append q).support
    rw [Walk.mem_support_append_iff]
    apply Or.inl
    have hds : d ∈ s.support := by
      change d ∈ (Walk.cons had r).support
      simp only [Walk.support_cons, List.mem_cons]
      exact Or.inr r.start_mem_support
    change d ∈ (s.concat hbe.symm).support
    rw [Walk.support_concat, List.mem_append]
    exact Or.inl hds
  let c' : G.Walk x x := c₁.rotate x hxc₁
  have hc' : c'.IsCycle := hc₁.rotate hxc₁
  have hdc' : d ∈ c'.support :=
    (Walk.mem_support_rotate_iff c₁ x hxc₁).mpr hdc₁
  have hdx : d ≠ x := by
    intro hdx
    exact (c.componentVerts_subset_outside K hdK) (hdx ▸ c.start_mem_support)
  refine ⟨c', hc', d, hdc', hdx, ?_⟩
  by_cases hbound : c'.IsBoundVertex d
  · exact Or.inl hbound
  · right
    have hnotall : ¬∀ z, G.Adj d z → z ∈ c'.support := by
      intro hall
      exact hbound ⟨hdc', hall⟩
    push Not at hnotall
    obtain ⟨z, hdz, hzout⟩ := hnotall
    have hac' : a ∈ c'.support := by
      apply (Walk.mem_support_rotate_iff c₁ x hxc₁).mpr
      change a ∈ (dpath.append q).support
      rw [Walk.mem_support_append_iff]
      exact Or.inl dpath.start_mem_support
    have hbc' : b ∈ c'.support := by
      apply (Walk.mem_support_rotate_iff c₁ x hxc₁).mpr
      change b ∈ (dpath.append q).support
      rw [Walk.mem_support_append_iff]
      exact Or.inl dpath.end_mem_support
    have hclosed {v w : V} (hv : v ∈ c.componentVerts K) (hvw : G.Adj v w)
        (hw : w ∈ c'.outside) : w ∈ c.componentVerts K := by
      by_cases hwc : w ∈ c.support
      · rcases hcover w hwc with hwp | hwq
        · have hwa : w ≠ a := fun hwa ↦ hw (hwa ▸ hac')
          have hwb : w ≠ b := fun hwb ↦ hw (hwb ▸ hbc')
          exact False.elim (hno w hwp hwa hwb ⟨hwc, v, hv, hvw.symm⟩)
        · exact False.elim (hw (by
            apply (Walk.mem_support_rotate_iff c₁ x hxc₁).mpr
            change w ∈ (dpath.append q).support
            rw [Walk.mem_support_append_iff]
            exact Or.inr hwq))
      · exact c.mem_componentVerts_of_adj K hv hvw hwc
    have hzK : z ∈ c.componentVerts K := hclosed hdK hdz hzout
    let z' : c'.outside := ⟨z, hzout⟩
    let L := (G.induce c'.outside).connectedComponentMk z'
    have hwalk {u v : c'.outside} (walk : (G.induce c'.outside).Walk u v)
        (hu : (u : V) ∈ c.componentVerts K) : (v : V) ∈ c.componentVerts K := by
      induction walk with
      | nil => exact hu
      | @cons _ t _ hadj walk ih =>
          exact ih (hclosed hu (induce_adj.mp hadj) t.property)
    have hsubset : c'.componentVerts L ⊆ c.componentVerts K := by
      rintro w ⟨w', hwL, rfl⟩
      have hzL : z' ∈ L.supp := ConnectedComponent.connectedComponentMk_mem
      obtain ⟨walk⟩ := L.reachable_of_mem_supp hzL hwL
      exact hwalk walk hzK
    refine ⟨L, (Set.ssubset_iff_of_subset hsubset).mpr ⟨d, hdK, ?_⟩⟩
    intro hdL
    exact (c'.componentVerts_subset_outside L hdL) hdc'

/-- **Říha's cycle lemma.** Let $G$ be a finite $2$-vertex-connected simple graph. Then for
every vertex $x$ of $G$ there is a cycle $c$ through $x$ and a vertex $y \ne x$ that is bound
to $c$: $y$ lies on $c$ and every neighbor of $y$ in $G$ lies on $c$. -/
public theorem IsVertexConnected.exists_cycle_bound_vertex
    {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.IsVertexConnected 2) (x : V) :
    ∃ c : G.Walk x x, c.IsCycle ∧ ∃ y, y ≠ x ∧ c.IsBoundVertex y := by
  classical
  obtain ⟨c₀, hc₀⟩ := hG.exists_cycle_through x
  by_cases hout : c₀.outside = ∅
  · obtain ⟨y, hyx, hy⟩ := hc₀.exists_boundVertex_of_outside_eq_empty hout
    exact ⟨c₀, hc₀, y, hyx, hy⟩
  have houtne : c₀.outside.Nonempty := Set.nonempty_iff_ne_empty.mpr hout
  let z₀ : c₀.outside := ⟨houtne.choose, houtne.choose_spec⟩
  let K₀ := (G.induce c₀.outside).connectedComponentMk z₀
  have hex : ∃ n, rihaCandidate G x n := by
    refine ⟨(c₀.componentVerts K₀).ncard, c₀, hc₀, K₀, rfl⟩
  obtain ⟨c, hc, K, hcard⟩ := Nat.find_spec hex
  obtain ⟨c', hc', y, hyc', hyx, hbound | ⟨L, hsmaller⟩⟩ :=
    hG.exists_bound_or_smaller_component hc K
  · exact ⟨c', hc', y, hyx, hbound⟩
  · have hcand : rihaCandidate G x (c'.componentVerts L).ncard :=
      ⟨c', hc', L, rfl⟩
    have hlt : (c'.componentVerts L).ncard < Nat.find hex := by
      have := Set.ncard_lt_ncard hsmaller
      omega
    exact False.elim (Nat.find_min hex hlt hcand)

end SimpleGraph
