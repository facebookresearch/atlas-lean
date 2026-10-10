/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Trails

import MathlibExt.Combinatorics.SimpleGraph.EulerCircuit

/-!
# Finite edge-indexed multigraphs

Parallel edges are represented by distinct elements of the edge type. The incidence subdivision
turns such a multigraph into a simple bipartite graph and transfers Euler circuits back to an
edge-distinguishing representation.
-/

@[expose] public section

namespace SimpleGraph

/-- A loopless multigraph whose parallel edges are distinguished by an edge type. -/
public structure EdgeIndexedMultigraph (V : Type*) (E : Type*) where
  /-- The unordered endpoints of an edge. -/
  ends : E → Sym2 V
  /-- No edge has two equal endpoints. -/
  loopless : ∀ e v, ends e ≠ s(v, v)

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- A walk that records the identity of every traversed multiedge. -/
public inductive IndexedWalk : V → V → Type _
  | nil (v : V) : IndexedWalk v v
  | cons {u v w : V} (e : E) (he : M.ends e = s(u, v))
      (p : IndexedWalk v w) : IndexedWalk u w

namespace IndexedWalk

/-- The vertices of an indexed walk, including both endpoints. -/
public def support {u v : V} : M.IndexedWalk u v → List V
  | .nil w => [w]
  | .cons _ _ p => u :: p.support

/-- The edge identities traversed by an indexed walk. -/
public def edges {u v : V} : M.IndexedWalk u v → List E
  | .nil _ => []
  | .cons e _ p => e :: p.edges

/-- An indexed walk is a trail when it uses no edge identity twice. -/
public def IsTrail {u v : V} (p : M.IndexedWalk u v) : Prop :=
  p.edges.Nodup

/-- An indexed walk is a trail exactly when its edge list has no duplicates. -/
public theorem isTrail_iff {u v : V} (p : M.IndexedWalk u v) :
    p.IsTrail ↔ p.edges.Nodup :=
  Iff.rfl

/-- An indexed trail is Eulerian when it uses every edge identity. -/
public def IsEulerian {u v : V} (p : M.IndexedWalk u v) : Prop :=
  p.IsTrail ∧ ∀ e, e ∈ p.edges

/-- An indexed walk is Eulerian exactly when it is a trail containing every edge identity. -/
public theorem isEulerian_iff {u v : V} (p : M.IndexedWalk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ p.edges :=
  Iff.rfl

/-- The support of the empty indexed walk is its sole vertex. -/
@[simp]
public theorem support_nil (v : V) : (IndexedWalk.nil v : M.IndexedWalk v v).support = [v] :=
  rfl

/-- Prepending an indexed edge prepends its initial vertex to the support. -/
@[simp]
public theorem support_cons {u v w : V} (e : E) (he : M.ends e = s(u, v))
    (p : M.IndexedWalk v w) : (IndexedWalk.cons e he p).support = u :: p.support :=
  rfl

/-- The empty indexed walk has no edges. -/
@[simp]
public theorem edges_nil (v : V) : (IndexedWalk.nil v : M.IndexedWalk v v).edges = [] :=
  rfl

/-- Prepending an indexed edge prepends its identity to the edge list. -/
@[simp]
public theorem edges_cons {u v w : V} (e : E) (he : M.ends e = s(u, v))
    (p : M.IndexedWalk v w) : (IndexedWalk.cons e he p).edges = e :: p.edges :=
  rfl

end IndexedWalk

/-- A vertex is incident with an edge when it belongs to the edge's endpoint pair. -/
public def Inc (v : V) (e : E) : Prop :=
  v ∈ M.ends e

/-- Incidence means membership in the unordered pair of edge endpoints. -/
@[simp]
public theorem inc_iff (v : V) (e : E) : M.Inc v e ↔ v ∈ M.ends e :=
  Iff.rfl

/-- The simple graph obtained by forgetting edge multiplicities. -/
public def underlying : SimpleGraph V :=
  fromEdgeSet (Set.range M.ends)

/-- Adjacency in the underlying simple graph means that some indexed edge has the given
endpoints. -/
@[simp]
public theorem underlying_adj {u v : V} :
    M.underlying.Adj u v ↔ ∃ e, M.ends e = s(u, v) := by
  rw [underlying, fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he⟩, _⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    refine ⟨⟨e, he⟩, ?_⟩
    intro huv
    subst v
    exact M.loopless e u he

namespace IndexedWalk

/-- Forget edge identities in an indexed walk. -/
public def toWalk {u v : V} : M.IndexedWalk u v → M.underlying.Walk u v
  | .nil w => .nil
  | .cons e he p => .cons (M.underlying_adj.mpr ⟨e, he⟩) p.toWalk

/-- Forgetting edge identities preserves the vertex support. -/
@[simp]
public theorem support_toWalk {u v : V} (p : M.IndexedWalk u v) :
    p.toWalk.support = p.support := by
  induction p with
  | nil => rfl
  | cons e he p ih => exact congrArg (fun l ↦ _ :: l) ih

/-- Forgetting edge identities maps each edge to its unordered endpoint pair. -/
@[simp]
public theorem edges_toWalk {u v : V} (p : M.IndexedWalk u v) :
    p.toWalk.edges = p.edges.map M.ends := by
  induction p with
  | nil => rfl
  | @cons u v w e he p ih =>
      change s(u, v) :: p.toWalk.edges = M.ends e :: List.map M.ends p.edges
      rw [he, ih]

/-- Forgetting edge identities preserves the number of traversed edges. -/
@[simp]
public theorem length_toWalk {u v : V} (p : M.IndexedWalk u v) :
    p.toWalk.length = p.edges.length := by
  calc
    p.toWalk.length = p.toWalk.edges.length := p.toWalk.length_edges.symm
    _ = p.edges.length := by rw [edges_toWalk, List.length_map]

end IndexedWalk

/-- The number of indexed edges incident with a vertex. -/
public noncomputable def degree (v : V) : ℕ :=
  {e | M.Inc v e}.ncard

/-- The multigraph degree is the cardinality of the set of incident edge identities. -/
public theorem degree_eq_ncard_inc (v : V) :
    M.degree v = {e | M.Inc v e}.ncard :=
  rfl

/-- Disjoint union of two indexed edge sets on the same vertex type. -/
public def disjointSum {F : Type*} (N : EdgeIndexedMultigraph V F) :
    EdgeIndexedMultigraph V (E ⊕ F) where
  ends
    | Sum.inl e => M.ends e
    | Sum.inr f => N.ends f
  loopless := by
    intro e v
    cases e with
    | inl e => exact M.loopless e v
    | inr f => exact N.loopless f v

/-- A left edge keeps its endpoints in a disjoint sum. -/
@[simp]
public theorem disjointSum_ends_inl {F : Type*} (N : EdgeIndexedMultigraph V F) (e : E) :
    (M.disjointSum N).ends (Sum.inl e) = M.ends e :=
  rfl

/-- A right edge keeps its endpoints in a disjoint sum. -/
@[simp]
public theorem disjointSum_ends_inr {F : Type*} (N : EdgeIndexedMultigraph V F) (f : F) :
    (M.disjointSum N).ends (Sum.inr f) = N.ends f :=
  rfl

private def disjointSumIncidenceEquiv {F : Type*} (N : EdgeIndexedMultigraph V F)
    (v : V) :
    {e : E ⊕ F // (M.disjointSum N).Inc v e} ≃
      {e : E // M.Inc v e} ⊕ {f : F // N.Inc v f} where
  toFun e := by
    rcases e with ⟨e, he⟩
    cases e with
    | inl e => exact Sum.inl ⟨e, he⟩
    | inr f => exact Sum.inr ⟨f, he⟩
  invFun e := by
    cases e with
    | inl e => exact ⟨Sum.inl e.1, e.2⟩
    | inr f => exact ⟨Sum.inr f.1, f.2⟩
  left_inv := by
    rintro ⟨e, he⟩
    cases e <;> rfl
  right_inv := by
    intro e
    cases e <;> rfl

/-- Degrees add under disjoint union of indexed edge sets. -/
public theorem disjointSum_degree {F : Type*} [Finite E] [Finite F]
    (N : EdgeIndexedMultigraph V F) (v : V) :
    (M.disjointSum N).degree v = M.degree v + N.degree v := by
  calc
    (M.disjointSum N).degree v =
        Nat.card {e : E ⊕ F // (M.disjointSum N).Inc v e} := by
      rw [degree]
      exact (Nat.card_coe_set_eq
        {e : E ⊕ F | (M.disjointSum N).Inc v e}).symm
    _ = Nat.card ({e : E // M.Inc v e} ⊕ {f : F // N.Inc v f}) :=
      Nat.card_congr (M.disjointSumIncidenceEquiv N v)
    _ = Nat.card {e : E // M.Inc v e} + Nat.card {f : F // N.Inc v f} :=
      Nat.card_sum
    _ = M.degree v + N.degree v := by
      rw [degree, degree]
      exact congrArg₂ (· + ·)
        (Nat.card_coe_set_eq {e : E | M.Inc v e})
        (Nat.card_coe_set_eq {f : F | N.Inc v f})

/-- Adding a disjoint family of indexed edges preserves connectedness. -/
public theorem disjointSum_connected_left {F : Type*}
    (N : EdgeIndexedMultigraph V F) (hM : M.underlying.Connected) :
    (M.disjointSum N).underlying.Connected := by
  let f : M.underlying →g (M.disjointSum N).underlying := {
    toFun := id
    map_rel' := by
      intro u v huv
      obtain ⟨e, he⟩ := M.underlying_adj.mp huv
      apply (M.disjointSum N).underlying_adj.mpr
      exact ⟨Sum.inl e, he⟩ }
  apply hM.map f
  intro v
  exact ⟨v, rfl⟩

/-- The bipartite simple graph obtained by subdividing every indexed edge once. -/
private def incidenceGraph : SimpleGraph (V ⊕ E) where
  Adj a b := match a, b with
    | Sum.inl v, Sum.inr e => M.Inc v e
    | Sum.inr e, Sum.inl v => M.Inc v e
    | _, _ => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

private instance [DecidableEq V] : DecidableRel M.incidenceGraph.Adj := by
  intro a b
  cases a <;> cases b <;> simp only [incidenceGraph, Inc] <;> infer_instance

/-- Incidence edges join original vertices to indexed edges. -/
@[simp]
private theorem incidenceGraph_adj_inl_inr (v : V) (e : E) :
    M.incidenceGraph.Adj (Sum.inl v) (Sum.inr e) ↔ M.Inc v e :=
  Iff.rfl

/-- Incidence adjacency is symmetric. -/
@[simp]
private theorem incidenceGraph_adj_inr_inl (e : E) (v : V) :
    M.incidenceGraph.Adj (Sum.inr e) (Sum.inl v) ↔ M.Inc v e :=
  Iff.rfl

/-- Two original vertices are not adjacent in the incidence subdivision. -/
@[simp]
private theorem not_incidenceGraph_adj_inl_inl (u v : V) :
    ¬M.incidenceGraph.Adj (Sum.inl u) (Sum.inl v) := by
  intro h
  exact h

/-- Two indexed edges are not adjacent in the incidence subdivision. -/
@[simp]
private theorem not_incidenceGraph_adj_inr_inr (e f : E) :
    ¬M.incidenceGraph.Adj (Sum.inr e) (Sum.inr f) := by
  intro h
  exact h

/-- Every indexed edge has two distinct endpoints. -/
private theorem exists_ends (e : E) :
    ∃ u v, u ≠ v ∧ M.ends e = s(u, v) := by
  induction h : M.ends e using Sym2.inductionOn with
  | _ u v =>
      refine ⟨u, v, ?_, rfl⟩
      intro huv
      subst v
      exact M.loopless e u h

/-- Incidence with an indexed edge witnesses adjacency in the underlying graph. -/
private theorem exists_underlying_adj_of_inc {v : V} {e : E} (h : M.Inc v e) :
    ∃ w, M.underlying.Adj v w := by
  obtain ⟨u, w, huw, he⟩ := M.exists_ends e
  rw [Inc, he] at h
  rcases Sym2.mem_iff.mp h with hvu | hvw
  · subst v
    exact ⟨w, M.underlying_adj.mpr ⟨e, he⟩⟩
  · subst v
    exact ⟨u, M.underlying_adj.mpr ⟨e, he.trans Sym2.eq_swap⟩⟩

/-- Reachability in the underlying graph lifts to reachability between original vertices of the
incidence subdivision. -/
private theorem reachable_inl {u v : V} (h : M.underlying.Reachable u v) :
    M.incidenceGraph.Reachable (Sum.inl u) (Sum.inl v) := by
  rw [reachable_iff_reflTransGen] at h ⊢
  apply h.lift' Sum.inl
  intro a b hab
  change Relation.ReflTransGen M.incidenceGraph.Adj (Sum.inl a) (Sum.inl b)
  obtain ⟨e, he⟩ := M.underlying_adj.mp hab
  have hae : M.incidenceGraph.Adj (Sum.inl a) (Sum.inr e) := by
    change M.Inc a e
    simp [Inc, he]
  have heb : M.incidenceGraph.Adj (Sum.inr e) (Sum.inl b) := by
    change M.Inc b e
    simp [Inc, he]
  exact (Relation.ReflTransGen.single hae).trans (Relation.ReflTransGen.single heb)

private theorem incidence_support_anchor
    (z : M.incidenceGraph.support) :
    ∃ v : M.underlying.support,
      M.incidenceGraph.Reachable z.1 (Sum.inl v.1) := by
  rcases z with ⟨z, hz⟩
  cases z with
  | inl v =>
      rw [M.incidenceGraph.mem_support] at hz
      obtain ⟨z, hvz⟩ := hz
      cases z with
      | inl w => exact False.elim (M.not_incidenceGraph_adj_inl_inl v w hvz)
      | inr e =>
          obtain ⟨w, hvw⟩ := M.exists_underlying_adj_of_inc hvz
          exact ⟨⟨v, M.underlying.mem_support.mpr ⟨w, hvw⟩⟩, ⟨Walk.nil⟩⟩
  | inr e =>
      obtain ⟨u, v, huv, he⟩ := M.exists_ends e
      have huv' : M.underlying.Adj u v := M.underlying_adj.mpr ⟨e, he⟩
      let u' : M.underlying.support :=
        ⟨u, M.underlying.mem_support.mpr ⟨v, huv'⟩⟩
      have heu : M.incidenceGraph.Adj (Sum.inr e) (Sum.inl u) := by
        change M.Inc u e
        simp [Inc, he]
      exact ⟨u', ⟨Walk.cons heu Walk.nil⟩⟩

/-- If the non-isolated vertices of the underlying multigraph are connected, then the same is
true in its incidence subdivision. -/
private theorem incidenceGraph_connectedSupport
    (hconn : (M.underlying.induce M.underlying.support).Connected) :
    (M.incidenceGraph.induce M.incidenceGraph.support).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro z w
    obtain ⟨u, hzu⟩ := M.incidence_support_anchor z
    obtain ⟨v, hwv⟩ := M.incidence_support_anchor w
    have huv : M.underlying.Reachable u.1 v.1 :=
      (hconn u v).map (Embedding.induce M.underlying.support).toHom
    have hzw : M.incidenceGraph.Reachable z.1 w.1 :=
      hzu.trans (M.reachable_inl huv) |>.trans hwv.symm
    exact hzw.induce_support z.2 w.2
  · obtain ⟨u⟩ := hconn.nonempty
    have hu := u.2
    rw [M.underlying.mem_support] at hu
    obtain ⟨v, huv⟩ := hu
    obtain ⟨e, he⟩ := M.underlying_adj.mp huv
    refine ⟨⟨Sum.inl u.1, M.incidenceGraph.mem_support.mpr ?_⟩⟩
    exact ⟨Sum.inr e, by simp [Inc, he]⟩

/-- Connectedness of the underlying simple graph implies connectedness of the incidence
subdivision. -/
private theorem incidenceGraph_connected (hM : M.underlying.Connected) :
    M.incidenceGraph.Connected := by
  obtain ⟨r⟩ := hM.nonempty
  have reach : ∀ z : V ⊕ E, M.incidenceGraph.Reachable (Sum.inl r) z := by
    intro z
    cases z with
    | inl v => exact M.reachable_inl (hM r v)
    | inr e =>
        obtain ⟨u, v, huv, he⟩ := M.exists_ends e
        apply (M.reachable_inl (hM r u)).trans
        exact ⟨Walk.cons (by simp [Inc, he]) Walk.nil⟩
  refine { preconnected := ?_, nonempty := ⟨Sum.inl r⟩ }
  intro a b
  exact (reach a).symm.trans (reach b)

/-- The degree of an original vertex in the incidence subdivision is its multigraph degree. -/
private theorem incidenceGraph_degree_inl [Fintype V] [Fintype E] [DecidableEq V] (v : V) :
    M.incidenceGraph.degree (Sum.inl v) = M.degree v := by
  classical
  have hset : M.incidenceGraph.neighborSet (Sum.inl v) =
      Sum.inr '' {e | M.Inc v e} := by
    ext z
    cases z <;> simp [mem_neighborSet]
  rw [← ncard_neighborSet, hset, Set.ncard_image_of_injective _ Sum.inr_injective]
  rfl

/-- Every indexed edge becomes a degree-two vertex in the incidence subdivision. -/
private theorem incidenceGraph_degree_inr [Fintype V] [Fintype E] [DecidableEq V] (e : E) :
    M.incidenceGraph.degree (Sum.inr e) = 2 := by
  classical
  have hset : M.incidenceGraph.neighborSet (Sum.inr e) =
      Sum.inl '' {v | M.Inc v e} := by
    ext z
    cases z <;> simp [mem_neighborSet]
  obtain ⟨u, v, huv, he⟩ := M.exists_ends e
  have hends : {w | M.Inc w e} = ({u, v} : Set V) := by
    ext w
    simp [Inc, he, Sym2.mem_iff]
  rw [← ncard_neighborSet, hset, Set.ncard_image_of_injective _ Sum.inl_injective,
    hends, Set.ncard_pair huv]

/-- The degree sum of a finite edge-indexed multigraph is even. -/
public theorem even_sum_degree [Fintype V] [Finite E] :
    Even (∑ v, M.degree v) := by
  classical
  let _ := Fintype.ofFinite E
  have htotal : Even (∑ z : V ⊕ E, M.incidenceGraph.degree z) := by
    rw [M.incidenceGraph.sum_degrees_eq_twice_card_edges]
    exact ⟨M.incidenceGraph.edgeFinset.card, by omega⟩
  rw [Fintype.sum_sum_type] at htotal
  simp_rw [M.incidenceGraph_degree_inl, M.incidenceGraph_degree_inr] at htotal
  have hedge : Even (∑ _e : E, 2) := by
    exact ⟨Fintype.card E, by simp; omega⟩
  exact (Nat.even_add.mp htotal).mpr hedge

/-- Keep the edge-index vertices from a list in the incidence subdivision. -/
private def edgeProjection : List (V ⊕ E) → List E
  | [] => []
  | Sum.inl _ :: l => edgeProjection l
  | Sum.inr e :: l => e :: edgeProjection l

private theorem edgeProjection_count [DecidableEq V] [DecidableEq E]
    (l : List (V ⊕ E)) (e : E) :
    (edgeProjection l).count e = l.countP (· = Sum.inr e) := by
  induction l with
  | nil => rfl
  | cons z l ih =>
      cases z with
      | inl v =>
          simpa [edgeProjection] using ih
      | inr f =>
          by_cases hfe : f = e
          · subst f
            simp [edgeProjection, List.count_cons_self, ih]
          · simp [edgeProjection, List.count_cons_of_ne hfe, hfe, ih]

private theorem walk_countP_edges_add_endpoints {W : Type*} [DecidableEq W]
    {H : SimpleGraph W} {u v : W} (p : H.Walk u v) (z : W) :
    p.edges.countP (z ∈ ·) + (if z = u then 1 else 0) + (if z = v then 1 else 0) =
      2 * p.support.countP (· = z) := by
  induction p with
  | @nil t =>
      by_cases hzt : z = t
      · subst z
        simp
      · simp [hzt, Ne.symm hzt]
  | @cons u w v h p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.countP_cons,
        SimpleGraph.Walk.support_cons]
      have huw : u ≠ w := H.ne_of_adj h
      by_cases hzu : z = u
      · subst z
        simp [huw, Sym2.mem_iff] at ih ⊢
        omega
      · by_cases hzw : z = w
        · subst z
          simp [hzu, Ne.symm hzu, Sym2.mem_iff] at ih ⊢
          omega
        · simp [hzu, Ne.symm hzu, hzw, Sym2.mem_iff] at ih ⊢
          omega

private theorem walk_two_mul_count_tail_support {W : Type*} [DecidableEq W]
    {H : SimpleGraph W} {u : W} (p : H.Walk u u) (z : W) :
    2 * p.support.tail.countP (· = z) = p.edges.countP (z ∈ ·) := by
  have h := walk_countP_edges_add_endpoints p z
  have hsupp : p.support.countP (· = z) =
      (if z = u then 1 else 0) + p.support.tail.countP (· = z) := by
    calc
      p.support.countP (· = z) =
          (u :: p.support.tail).countP (· = z) := by
        exact congrArg (List.countP (· = z)) p.cons_tail_support.symm
      _ = (if z = u then 1 else 0) + p.support.tail.countP (· = z) := by
        by_cases hzu : z = u
        · subst z
          simp only [List.countP_cons, decide_eq_true_eq]
          omega
        · simp only [List.countP_cons, decide_eq_true_eq, hzu, Ne.symm hzu]
          exact Nat.add_comm _ _
  rw [hsupp] at h
  by_cases hzu : z = u
  · simp [hzu] at h ⊢
    omega
  · simp [hzu] at h ⊢
    omega

/-- An incidence trail collapsed to an indexed walk, with its edge-list identity. -/
private structure IncidenceCollapse [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) where
  walk : M.IndexedWalk u v
  edges_eq : walk.edges = edgeProjection p.support

/-- Collapse an incidence trail while retaining the edge-list identity. -/
private def collapseIncidence [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
    M.IncidenceCollapse p := by
  cases hp₀ : p with
  | nil => exact ⟨.nil u, rfl⟩
  | @cons _ z _ h p =>
      cases z with
      | inl w => exact False.elim (M.not_incidenceGraph_adj_inl_inl u w h)
      | inr e =>
          cases hp₁ : p with
          | @cons _ z _ h' p' =>
              cases z with
              | inr f => exact False.elim (M.not_incidenceGraph_adj_inr_inr e f h')
              | inl w =>
                  rw [hp₀, hp₁] at hp
                  have huw : u ≠ w := by
                    intro huw
                    subst w
                    have hnot := (SimpleGraph.Walk.isTrail_cons h _).mp hp |>.2
                    apply hnot
                    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
                    left
                    exact Sym2.eq_swap
                  have he : M.ends e = s(u, w) :=
                    (Sym2.mem_and_mem_iff huw).mp ⟨h, h'⟩
                  have hdecr : p'.length < p.length := by
                    rw [hp₁, SimpleGraph.Walk.length_cons]
                    omega
                  let tail := collapseIncidence p' hp.of_cons.of_cons
                  refine ⟨IndexedWalk.cons e he tail.walk, ?_⟩
                  simp only [SimpleGraph.Walk.support_cons, edgeProjection]
                  exact congrArg (e :: ·) tail.edges_eq
termination_by p.length
decreasing_by
  apply lt_trans hdecr
  rw [hp₀, SimpleGraph.Walk.length_cons]
  omega

/-- Collapse an incidence-graph trail between original vertices to an edge-indexed walk. -/
private def indexedWalkOfIncidence [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
    M.IndexedWalk u v :=
  (M.collapseIncidence p hp).walk

/-- The collapsed indexed walk records exactly the edge-index vertices of the incidence walk. -/
private theorem indexedWalkOfIncidence_edges [DecidableEq V] {u v : V}
    (p : M.incidenceGraph.Walk (Sum.inl u) (Sum.inl v)) (hp : p.IsTrail) :
    (M.indexedWalkOfIncidence p hp).edges = edgeProjection p.support :=
  (M.collapseIncidence p hp).edges_eq

/-- A connected finite edge-indexed multigraph of even degrees has an Euler circuit in its
incidence subdivision. The indexed-edge vertices distinguish parallel edges. -/
private theorem exists_eulerian [Finite V] [Finite E] [DecidableEq V] [DecidableEq E]
    (hconn : M.underlying.Connected) (heven : ∀ v, Even (M.degree v)) :
    ∃ (z : V ⊕ E) (p : M.incidenceGraph.Walk z z), p.IsEulerian := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  apply (M.incidenceGraph_connected hconn).exists_isEulerian
  intro z
  cases z with
  | inl v =>
      rw [M.incidenceGraph_degree_inl]
      exact heven v
  | inr e =>
      rw [M.incidenceGraph_degree_inr]
      exact even_two

/-- A connected finite edge-indexed multigraph of even degrees has an edge-distinguishing
Euler circuit. -/
public theorem exists_indexedEulerian [Finite V] [Finite E]
    (hconn : M.underlying.Connected) (heven : ∀ v, Even (M.degree v)) :
    ∃ (u : V) (p : M.IndexedWalk u u), p.IsEulerian := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  by_cases hE : Nonempty E
  · obtain ⟨e⟩ := hE
    obtain ⟨z, p, hp⟩ := M.exists_eulerian hconn heven
    obtain ⟨u, v, huv, he⟩ := M.exists_ends e
    have hue : M.incidenceGraph.Adj (Sum.inl u) (Sum.inr e) := by
      simp [Inc, he]
    have hu_support : Sum.inl u ∈ p.support :=
      hp.mem_support_of_not_isIsolated hue.not_isIsolated_left
    let q := p.rotate (Sum.inl u) hu_support
    have hq_trail : q.IsTrail := hp.isTrail.rotate hu_support
    have hq_eulerian : q.IsEulerian := by
      apply hq_trail.isEulerian_of_forall_mem
      intro f hf
      apply (p.rotate_edges (Sum.inl u) hu_support).mem_iff.mpr
      exact hp.mem_edges_iff.mpr hf
    have htail_count (f : E) :
        q.support.tail.countP (· = Sum.inr f) = 1 := by
      have hcount := walk_two_mul_count_tail_support q (Sum.inr f)
      rw [hq_eulerian.countP_edges_eq_degree,
        M.incidenceGraph_degree_inr] at hcount
      omega
    have hprojection : edgeProjection q.support = edgeProjection q.support.tail := by
      calc
        edgeProjection q.support =
            edgeProjection (Sum.inl u :: q.support.tail) := by
          exact congrArg edgeProjection q.cons_tail_support.symm
        _ = edgeProjection q.support.tail := rfl
    let r := M.indexedWalkOfIncidence q hq_trail
    have hr_count (f : E) : r.edges.count f = 1 := by
      rw [M.indexedWalkOfIncidence_edges q hq_trail, hprojection,
        edgeProjection_count]
      exact htail_count f
    refine ⟨u, r, ?_⟩
    constructor
    · apply List.nodup_iff_count_le_one.mpr
      intro f
      rw [hr_count f]
    · intro f
      apply List.count_pos_iff.mp
      rw [hr_count f]
      omega
  · let _ : IsEmpty E := ⟨fun e ↦ hE ⟨e⟩⟩
    obtain ⟨u⟩ := hconn.nonempty
    refine ⟨u, .nil u, ?_⟩
    exact ⟨by simp [IndexedWalk.IsTrail], fun e ↦ isEmptyElim e⟩

/-- A finite edge-indexed multigraph with connected non-isolated support and even degrees has
an Euler circuit in its incidence subdivision. -/
private theorem exists_eulerian_connectedSupport [Finite V] [Finite E]
    [DecidableEq V] [DecidableEq E]
    (hconn : (M.underlying.induce M.underlying.support).Connected)
    (heven : ∀ v, Even (M.degree v)) :
    ∃ (z : V ⊕ E) (p : M.incidenceGraph.Walk z z), p.IsEulerian := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  apply ConnectedSupport.exists_isEulerian (M.incidenceGraph_connectedSupport hconn)
  intro z
  cases z with
  | inl v =>
      rw [M.incidenceGraph_degree_inl]
      exact heven v
  | inr e =>
      rw [M.incidenceGraph_degree_inr]
      exact even_two

/-- A finite edge-indexed multigraph with connected non-isolated support and even degrees has
an edge-distinguishing Euler circuit. -/
public theorem exists_indexedEulerian_connectedSupport [Finite V] [Finite E]
    (hconn : (M.underlying.induce M.underlying.support).Connected)
    (heven : ∀ v, Even (M.degree v)) :
    ∃ (u : V) (p : M.IndexedWalk u u), p.IsEulerian := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  by_cases hE : Nonempty E
  · obtain ⟨e⟩ := hE
    obtain ⟨z, p, hp⟩ := M.exists_eulerian_connectedSupport hconn heven
    obtain ⟨u, v, huv, he⟩ := M.exists_ends e
    have hue : M.incidenceGraph.Adj (Sum.inl u) (Sum.inr e) := by
      simp [Inc, he]
    have hu_support : Sum.inl u ∈ p.support :=
      hp.mem_support_of_not_isIsolated hue.not_isIsolated_left
    let q := p.rotate (Sum.inl u) hu_support
    have hq_trail : q.IsTrail := hp.isTrail.rotate hu_support
    have hq_eulerian : q.IsEulerian := by
      apply hq_trail.isEulerian_of_forall_mem
      intro f hf
      apply (p.rotate_edges (Sum.inl u) hu_support).mem_iff.mpr
      exact hp.mem_edges_iff.mpr hf
    have htail_count (f : E) :
        q.support.tail.countP (· = Sum.inr f) = 1 := by
      have hcount := walk_two_mul_count_tail_support q (Sum.inr f)
      rw [hq_eulerian.countP_edges_eq_degree,
        M.incidenceGraph_degree_inr] at hcount
      omega
    have hprojection : edgeProjection q.support = edgeProjection q.support.tail := by
      calc
        edgeProjection q.support =
            edgeProjection (Sum.inl u :: q.support.tail) := by
          exact congrArg edgeProjection q.cons_tail_support.symm
        _ = edgeProjection q.support.tail := rfl
    let r := M.indexedWalkOfIncidence q hq_trail
    have hr_count (f : E) : r.edges.count f = 1 := by
      rw [M.indexedWalkOfIncidence_edges q hq_trail, hprojection,
        edgeProjection_count]
      exact htail_count f
    refine ⟨u, r, ?_⟩
    constructor
    · apply List.nodup_iff_count_le_one.mpr
      intro f
      rw [hr_count f]
    · intro f
      apply List.count_pos_iff.mp
      rw [hr_count f]
      omega
  · let _ : IsEmpty E := ⟨fun e ↦ hE ⟨e⟩⟩
    obtain ⟨u⟩ := hconn.nonempty
    have hu := M.underlying.mem_support.mp u.2
    obtain ⟨v, huv⟩ := hu
    obtain ⟨e, he⟩ := M.underlying_adj.mp huv
    exact isEmptyElim e

/-- The line graph of an edge-indexed multigraph: vertices are edge identities,
adjacent when distinct and sharing an endpoint. Parallel edges are adjacent. -/
public def lineGraph : SimpleGraph E where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ ∃ v, M.Inc v e₁ ∧ M.Inc v e₂
  symm := ⟨by
    intro e₁ e₂ h
    obtain ⟨hne, v, hv₁, hv₂⟩ := h
    exact ⟨Ne.symm hne, v, hv₂, hv₁⟩⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩

/-- Adjacency in the multigraph line graph: distinct edges sharing a vertex. -/
@[simp]
public theorem lineGraph_adj {e₁ e₂ : E} :
    M.lineGraph.Adj e₁ e₂ ↔ e₁ ≠ e₂ ∧ ∃ v, M.Inc v e₁ ∧ M.Inc v e₂ :=
  Iff.rfl

/-- The maximum degree of a finite edge-indexed multigraph. Requires finite edge
identities: `M.degree` counts via `Set.ncard`, which collapses infinite
incident sets, so without `[Finite E]` this could report `0` for a genuinely
infinite-degree multigraph. -/
public noncomputable def maxDegree [Fintype V] [Finite E] : ℕ :=
  Finset.univ.sup M.degree

/-- Every vertex degree is bounded by the maximum degree. -/
public theorem degree_le_maxDegree [Fintype V] [Finite E] (v : V) :
    M.degree v ≤ M.maxDegree :=
  Finset.le_sup (Finset.mem_univ v)

/-- The multigraph degree counts incident edge identities. -/
public theorem filter_inc_card [Fintype E] (v : V)
    [DecidablePred fun e => M.Inc v e] :
    (Finset.univ.filter (fun e => M.Inc v e)).card = M.degree v := by
  classical
  change (Finset.univ.filter (fun e => M.Inc v e)).card = {e | M.Inc v e}.ncard
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

end EdgeIndexedMultigraph
end SimpleGraph
