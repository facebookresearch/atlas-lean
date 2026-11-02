/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.StrongSquareCycle
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

import MathlibExt.Combinatorics.SimpleGraph.Contraction
import MathlibExt.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
import MathlibExt.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic

/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- A cycle has as many support vertices as edges. -/
private theorem IsCycle.ncard_support_eq_length [Finite V] {c : G.Walk x x}
    (hc : c.IsCycle) : {v | v ∈ c.support}.ncard = c.length := by
  classical
  let _ := Fintype.ofFinite V
  have hnil := hc.not_nil
  have htail_support : c.tail.support = c.support.tail :=
    c.support_tail_of_not_nil hnil
  have hmem : ∀ v, v ∈ c.tail.support ↔ v ∈ c.support := by
    intro v
    constructor
    · intro hv
      rw [htail_support] at hv
      exact List.mem_of_mem_tail hv
    · intro hv
      rw [htail_support]
      rcases List.mem_cons.mp (c.cons_tail_support ▸ hv) with hvx | hv
      · subst v
        have hend : x ∈ c.tail.support := c.tail.end_mem_support
        rwa [htail_support] at hend
      · exact hv
  have hfinset : {v | v ∈ c.support}.toFinset = c.tail.support.toFinset := by
    ext v
    rw [Set.mem_toFinset, List.mem_toFinset]
    exact (hmem v).symm
  calc
    {v | v ∈ c.support}.ncard = c.tail.support.toFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      exact congrArg Finset.card hfinset
    _ = c.tail.support.length := List.toFinset_card_of_nodup hc.isPath_tail.support_nodup
    _ = c.length := by
      rw [c.tail.length_support, Walk.length_tail]
      have hpos := Walk.not_nil_iff_lt_length.mp hnil
      omega

/-- Dropping the repeated final vertex of a cycle does not change support membership. -/
private theorem IsCycle.mem_dropLast_support_iff {c : G.Walk x x}
    (hc : c.IsCycle) (v : V) :
    v ∈ c.support.dropLast ↔ v ∈ c.support := by
  constructor
  · exact List.mem_of_mem_dropLast
  · intro hv
    have hvTail : v ∈ c.support.tail := by
      rcases List.mem_cons.mp (c.cons_tail_support ▸ hv) with rfl | hv
      · exact c.end_mem_tail_support hc.not_nil
      · exact hv
    exact c.tail_support_perm_dropLast_support.mem_iff.mp hvTail

/-- The edge positions of a cycle are in bijection with its support vertices. -/
private noncomputable def IsCycle.finLengthEquivSupport {c : G.Walk x x}
    (hc : c.IsCycle) : Fin c.length ≃ {v // v ∈ c.support} := by
  classical
  have hlength : c.support.dropLast.length = c.length := by
    rw [List.length_dropLast, c.length_support]
    omega
  let eSupport : {v // v ∈ c.support.dropLast} ≃ {v // v ∈ c.support} := {
    toFun := fun v ↦ ⟨v, (hc.mem_dropLast_support_iff v).mp v.property⟩
    invFun := fun v ↦ ⟨v, (hc.mem_dropLast_support_iff v).mpr v.property⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl }
  exact (finCongr hlength.symm).trans
    ((hc.nodup_dropLast_support.getEquiv).trans eSupport)

/-- The cycle-support equivalence sends an edge position to the vertex at that position. -/
@[simp]
private theorem IsCycle.finLengthEquivSupport_apply {c : G.Walk x x}
    (hc : c.IsCycle) (i : Fin c.length) :
    (hc.finLengthEquivSupport i).1 = c.getVert i := by
  classical
  simp [IsCycle.finLengthEquivSupport, c.getVert_eq_support_getElem i.isLt.le]

/-- The graph induced by the vertices outside a closed walk. -/
private def outsideGraph (c : G.Walk x x) : SimpleGraph {v // v ∉ c.support} :=
  G.induce {v | v ∉ c.support}

/-- The original vertices belonging to one connected component outside a closed walk. -/
private def componentVertices (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) : Set V :=
  Subtype.val '' D.supp

/-- Membership in `componentVertices` retains a canonical outside-vertex witness. -/
private theorem mem_componentVertices_iff (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) (v : V) :
    v ∈ c.componentVertices D ↔
      ∃ hv : v ∉ c.support, (⟨v, hv⟩ : {w // w ∉ c.support}) ∈ D.supp := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hD⟩
    exact ⟨⟨v, hv⟩, hD, rfl⟩

/-- Every vertex in an outside component lies outside the walk. -/
private theorem componentVertices_subset_compl (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    c.componentVertices D ⊆ {v | v ∉ c.support} := by
  rintro v ⟨w, _, rfl⟩
  exact w.property

/-- An outside component contains an original vertex. -/
private theorem componentVertices_nonempty (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    (c.componentVertices D).Nonempty := by
  obtain ⟨w, hw⟩ := D.nonempty_supp
  exact ⟨w, w, hw, rfl⟩

/-- The cycle lies in the complement of each outside component. -/
private theorem support_subset_componentVertices_compl (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    {v | v ∈ c.support} ⊆ (c.componentVertices D)ᶜ := by
  intro v hvc hvD
  exact (c.componentVertices_subset_compl D hvD) hvc

/-- The complement of an outside component contains at least the three vertices of the cycle. -/
private theorem IsCycle.three_le_ncard_componentVertices_compl [Finite V]
    {c : G.Walk x x} (hc : c.IsCycle) (D : c.outsideGraph.ConnectedComponent) :
    3 ≤ (c.componentVertices D)ᶜ.ncard := by
  calc
    3 ≤ c.length := hc.three_le_length
    _ = {v | v ∈ c.support}.ncard := hc.ncard_support_eq_length.symm
    _ ≤ (c.componentVertices D)ᶜ.ncard :=
      Set.ncard_le_ncard (c.support_subset_componentVertices_compl D)

private def componentGraphHom (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    D.toSimpleGraph →g G.induce (c.componentVertices D) where
  toFun w := ⟨w.1.1, w.1, w.2, rfl⟩
  map_rel' := by
    intro u v huv
    exact huv

/-- The graph induced by the original vertices of an outside component is connected. -/
private theorem componentVertices_connected (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    (G.induce (c.componentVertices D)).Connected := by
  apply D.connected_toSimpleGraph.map (componentGraphHom c D)
  rintro ⟨v, w, hw, hv⟩
  subst v
  exact ⟨⟨w, hw⟩, rfl⟩

/-- An edge from an outside component to another vertex outside the walk stays in that
component. -/
private theorem mem_componentVertices_of_adj_of_not_mem (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) {u v : V}
    (hu : u ∈ c.componentVertices D) (huv : G.Adj u v) (hv : v ∉ c.support) :
    v ∈ c.componentVertices D := by
  obtain ⟨hu_out, huD⟩ := (c.mem_componentVertices_iff D u).mp hu
  apply (c.mem_componentVertices_iff D v).mpr
  refine ⟨hv, ?_⟩
  have hadj : c.outsideGraph.Adj ⟨u, hu_out⟩ ⟨v, hv⟩ := huv
  exact D.mem_supp_of_adj_mem_supp huD hadj

/-- Every neighbor outside an outside component lies on the walk. -/
private theorem mem_support_of_adj_of_not_mem_componentVertices (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) {u v : V}
    (hu : u ∈ c.componentVertices D) (huv : G.Adj u v)
    (hv : v ∉ c.componentVertices D) :
    v ∈ c.support := by
  by_contra hvc
  exact hv (c.mem_componentVertices_of_adj_of_not_mem D hu huv hvc)

/-- A singleton component outside a cycle has two distinct attachment vertices on the cycle. -/
private theorem IsVertexConnected.exists_two_attachments_of_component_ncard_eq_one
    [Fintype V] (hG : G.IsVertexConnected 2) (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent)
    (hcard : (c.componentVertices D).ncard = 1) :
    ∃ u ∈ c.componentVertices D, ∃ a ∈ c.support, ∃ b ∈ c.support,
      a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
  classical
  obtain ⟨u, hu⟩ := c.componentVertices_nonempty D
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hcard
  have hwu : w = u := by
    rw [hw] at hu
    simpa using hu.symm
  subst w
  have hdeg : 1 < (G.neighborSet u).ncard := by
    rw [G.ncard_neighborSet]
    have := hG.two_le_degree u
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp hdeg
  have hua : G.Adj u a := (mem_neighborSet G u a).mp ha
  have hub : G.Adj u b := (mem_neighborSet G u b).mp hb
  have haC : a ∈ c.support := by
    by_contra haC
    have haD := c.mem_componentVertices_of_adj_of_not_mem D hu hua haC
    have hau : a = u := by simpa [hw] using haD
    exact (G.ne_of_adj hua) hau.symm
  have hbC : b ∈ c.support := by
    by_contra hbC
    have hbD := c.mem_componentVertices_of_adj_of_not_mem D hu hub hbC
    have hbu : b = u := by simpa [hw] using hbD
    exact (G.ne_of_adj hub) hbu.symm
  exact ⟨u, hu, a, haC, b, hbC, hab, hua, hub⟩

end Walk

end SimpleGraph

/-! ## ComponentContraction -/


namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- In the component contraction, adjacency to the contraction vertex is exactly attachment to
the cycle. -/
@[simp]
private theorem contractOutside_component_adj_none {c : G.Walk x x}
    (D : c.outsideGraph.ConnectedComponent) (u : c.componentVertices D) :
    (G.contractOutside (c.componentVertices D)).Adj (some u) none ↔
      ∃ v ∈ c.support, G.Adj u v := by
  rw [contractOutside_adj_none]
  constructor
  · rintro ⟨v, hvD, huv⟩
    exact ⟨v, c.mem_support_of_adj_of_not_mem_componentVertices D u.property huv hvD, huv⟩
  · rintro ⟨v, hvc, huv⟩
    exact ⟨v, c.support_subset_componentVertices_compl D hvc, huv⟩

/-- A contraction-square edge between surviving vertices that is not present in the original
square uses the contraction vertex as its common neighbor. -/
private theorem contractOutside_square_adj_some_not_square {S : Set V} (a b : S)
    (hab : (G.contractOutside S).square.Adj (some a) (some b))
    (hnot : ¬G.square.Adj a b) :
    (G.contractOutside S).Adj (some a) none ∧
      (G.contractOutside S).Adj (some b) none := by
  have hne : (a : V) ≠ b := fun h ↦ hab.1 (congrArg some (Subtype.ext h))
  rcases hab.2 with hdirect | ⟨w, haw, hwb⟩
  · exact False.elim (hnot ⟨hne,
      Or.inl ((contractOutside_adj_some G S a b).mp hdirect)⟩)
  · cases w with
    | none => exact ⟨haw, hwb.symm⟩
    | some d =>
        have had : G.Adj a d := (contractOutside_adj_some G S a d).mp haw
        have hdb : G.Adj d b := (contractOutside_adj_some G S d b).mp hwb
        exact False.elim (hnot ⟨hne, Or.inr ⟨d, had, hdb⟩⟩)

/-- A nontrivial component outside a cycle gives a 2-connected contraction. -/
private theorem IsCycle.component_contractOutside_isVertexConnected
    [Fintype V] {c : G.Walk x x} (_hc : c.IsCycle) (hG : G.IsVertexConnected 2)
    (D : c.outsideGraph.ConnectedComponent) [Fintype (c.componentVertices D)]
    (hD : 1 < (c.componentVertices D).ncard) :
    (G.contractOutside (c.componentVertices D)).IsVertexConnected 2 := by
  classical
  have hDcard : 1 < Fintype.card (c.componentVertices D) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hD
  apply hG.contractOutside hDcard (c.componentVertices_connected D)
  exact ⟨x, c.support_subset_componentVertices_compl D c.start_mem_support⟩

/-- Contracting the complement of a cycle component strictly lowers the vertex count. -/
private theorem IsCycle.card_component_contractOutside_lt
    [Finite V] {c : G.Walk x x} (hc : c.IsCycle)
    (D : c.outsideGraph.ConnectedComponent) :
    Nat.card (Option (c.componentVertices D)) < Nat.card V := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (c.componentVertices D)
  have hlt := card_contractOutside_lt (c.componentVertices D) (by
    have hthree := hc.three_le_ncard_componentVertices_compl D
    have hncard : (c.componentVertices D)ᶜ.ncard =
        Fintype.card ↥((c.componentVertices D)ᶜ) := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    rw [hncard] at hthree
    omega)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hlt

end Walk

end SimpleGraph

/-! ## HamiltonianCycle helpers -/

namespace SimpleGraph

/-- A property holding at both neighbors of the start of a cycle holds at the other endpoint of
every cycle edge incident with the start. -/
private theorem Walk.IsCycle.property_of_mem_edges_at_start {V : Type*} {G : SimpleGraph V}
    {x v : V} {p : G.Walk x x} (hp : p.IsCycle) (P : V → Prop)
    (hfirst : P p.snd) (hlast : P p.penultimate)
    (he : s(x, v) ∈ p.edges) : P v := by
  have hadj : p.toSubgraph.Adj x v := Walk.adj_toSubgraph_iff_mem_edges.mpr he
  have hv : v ∈ p.toSubgraph.neighborSet x := hadj
  rw [hp.neighborSet_toSubgraph_endpoint] at hv
  rcases hv with rfl | rfl
  · exact hfirst
  · exact hlast

end SimpleGraph

/-! ## StrongSquareCycle listing -/

namespace SimpleGraph

/-- A rooted cyclic listing witnessing a Hamiltonian cycle in the square, with original-graph
edges at the root. -/
private structure StrongSquareCycleListing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) where
  vertices : List V
  first : V
  last : V
  frontRest : List V
  backRest : List V
  front_shape : vertices = x :: first :: frontRest
  back_shape : vertices = backRest ++ [last, x]
  four_le_length : 4 ≤ vertices.length
  square_chain : vertices.IsChain G.square.Adj
  tail_nodup : vertices.tail.Nodup
  mem_tail : ∀ v, v ∈ vertices.tail
  first_adj : G.Adj x first
  last_adj : G.Adj last x

/-- Turn a rooted cyclic listing into the corresponding rooted Hamiltonian cycle. -/
private theorem StrongSquareCycleListing.toHasStrongSquareCycle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x : V}
    (L : G.StrongSquareCycleListing x) : G.HasStrongSquareCycle x := by
  let l := L.vertices
  have hl_four : 4 ≤ l.length := L.four_le_length
  have hne : l ≠ [] := by simp [l, L.front_shape]
  have hhead : l.head hne = x := by
    simp [l, L.front_shape]
  have hgetLast : l.getLast hne = x := by
    simp [l, L.back_shape]
  let q := Walk.ofSupport l hne L.square_chain
  let p : G.square.Walk x x := q.copy hhead hgetLast
  have hp_length : p.length = l.length - 1 := by
    simp only [p, q, Walk.length_copy, Walk.length_ofSupport]
  have hp_not_nil : ¬p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hp_length]
    omega
  have hp_support : p.support = l := by
    simp only [p, q, Walk.support_copy, Walk.support_ofSupport]
  have hp_cycle : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def, p.support_tail_of_not_nil hp_not_nil, hp_support]
      exact L.tail_nodup
    · omega
  have hp_hamiltonian : p.tail.IsHamiltonian := by
    apply hp_cycle.isPath_tail.isHamiltonian_of_mem
    intro v
    rw [p.support_tail_of_not_nil hp_not_nil, hp_support]
    exact L.mem_tail v
  have hsnd : p.snd = L.first := by
    calc
      p.snd = p.support[1]'(by simpa [Walk.not_nil_iff_lt_length] using hp_not_nil) :=
        p.snd_eq_support_getElem_one hp_not_nil
      _ = l[1]'(by omega) := by simp only [hp_support]
      _ = L.first := by simp [l, L.front_shape]
  have hpenultimate : p.penultimate = L.last := by
    calc
      p.penultimate = p.support[p.length - 1] :=
        p.support_getElem_length_sub_one_eq_penultimate.symm
      _ = l[p.length - 1]'(by rw [← hp_support]; get_elem_tactic) := by
        simp only [hp_support]
      _ = l[l.length - 2]'(by omega) := by
        congr 1
        omega
      _ = L.last := by simp [l, L.back_shape]
  refine ⟨p, ⟨hp_cycle, hp_hamiltonian⟩, ?_, ?_⟩
  · rw [hsnd]
    exact L.first_adj
  · rw [hpenultimate]
    exact L.last_adj

end SimpleGraph

/-! ## ComponentTrailCover -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- A finite indexed multigraph covering one component outside a cycle. -/
private structure ComponentTrailCover (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) where
  /-- Edge identities, including identities for parallel copies. -/
  Edge : Type u
  edge_finite : Finite Edge
  /-- The indexed multigraph carried by the cover. -/
  multigraph : EdgeIndexedMultigraph V Edge
  /-- Every cover edge is an edge of the square. -/
  square_adj : ∀ e, multigraph.ends e ∈ G.square.edgeSet
  /-- Every cover edge has an endpoint in the component. -/
  meets_component : ∀ e, ∃ v ∈ c.componentVertices D, v ∈ multigraph.ends e
  /-- The other endpoints lie either in the component or on the cycle. -/
  endpoints_mem : ∀ e v, v ∈ multigraph.ends e →
    v ∈ c.componentVertices D ∨ v ∈ c.support
  /-- Edges incident with the cycle are original graph edges. -/
  cycle_edge : ∀ e u v, multigraph.ends e = s(u, v) →
    (u ∈ c.support ∨ v ∈ c.support) → G.Adj u v
  /-- Each component vertex has degree two in the cover. -/
  degree_eq_two : ∀ v ∈ c.componentVertices D, multigraph.degree v = 2
  /-- Each component vertex is connected by cover edges to the cycle. -/
  reachable_cycle : ∀ v ∈ c.componentVertices D,
    ∃ w ∈ c.support, multigraph.underlying.Reachable v w

attribute [instance] ComponentTrailCover.edge_finite

private def singletonCoverEnds (u a b : V) (i : Fin 2) : Sym2 V :=
  if i = 0 then s(u, a) else s(u, b)

private theorem singletonCoverEnds_mem_left (u a b : V) (i : Fin 2) :
    u ∈ singletonCoverEnds u a b i := by
  by_cases hi : i = 0
  · simp [singletonCoverEnds, hi]
  · simp [singletonCoverEnds, hi]

/-- A singleton outside component is covered by its two attachment edges. -/
private theorem IsVertexConnected.singletonComponentTrailCover [Fintype V]
    (hG : G.IsVertexConnected 2) (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent)
    (hcard : (c.componentVertices D).ncard = 1) :
    Nonempty (c.ComponentTrailCover D) := by
  classical
  obtain ⟨u, hu, a, ha, b, hb, hab, hua, hub⟩ :=
    SimpleGraph.Walk.IsVertexConnected.exists_two_attachments_of_component_ncard_eq_one
      hG c D hcard
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hcard
  have hwu : w = u := by
    rw [hw] at hu
    simpa using hu.symm
  subst w
  let M : EdgeIndexedMultigraph V (ULift.{u} (Fin 2)) := {
    ends := fun i ↦ singletonCoverEnds u a b i.down
    loopless := by
      intro i v hiv
      have hedge : singletonCoverEnds u a b i.down ∈ G.edgeSet := by
        by_cases hi : i.down = 0
        · simp [singletonCoverEnds, hi, G.mem_edgeSet, hua]
        · simp [singletonCoverEnds, hi, G.mem_edgeSet, hub]
      rw [hiv] at hedge
      exact G.loopless.irrefl v (G.mem_edgeSet.mp hedge) }
  refine ⟨{
    Edge := ULift.{u} (Fin 2)
    edge_finite := inferInstance
    multigraph := M
    square_adj := ?_
    meets_component := ?_
    endpoints_mem := ?_
    cycle_edge := ?_
    degree_eq_two := ?_
    reachable_cycle := ?_ }⟩
  · intro i
    rcases i with ⟨i⟩
    by_cases hi : i = 0
    · subst i
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hua, Or.inl hua⟩
    · have hi1 := Fin.eq_one_of_ne_zero i hi
      subst i
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hub, Or.inl hub⟩
  · intro i
    exact ⟨u, hu, singletonCoverEnds_mem_left u a b i.down⟩
  · intro i v hv
    rcases i with ⟨i⟩
    by_cases hi : i = 0
    · subst i
      change v ∈ s(u, a) at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr ha
    · have hi1 := Fin.eq_one_of_ne_zero i hi
      subst i
      change v ∈ s(u, b) at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr hb
  · intro i v z hiz _
    rcases i with ⟨i⟩
    have hedge : s(v, z) ∈ G.edgeSet := by
      rw [← hiz]
      by_cases hi : i = 0
      · simpa [M, singletonCoverEnds, hi] using G.mem_edgeSet.mpr hua
      · simpa [M, singletonCoverEnds, hi] using G.mem_edgeSet.mpr hub
    exact G.mem_edgeSet.mp hedge
  · intro v hv
    have hvu : v = u := by
      simpa [hw] using hv
    subst v
    have hset : {i : ULift.{u} (Fin 2) | M.Inc u i} = Set.univ := by
      ext i
      constructor
      · intro
        trivial
      · intro
        exact singletonCoverEnds_mem_left u a b i.down
    rw [EdgeIndexedMultigraph.degree, hset, Set.ncard_univ, Nat.card_ulift,
      Nat.card_fin]
  · intro v hv
    have hvu : v = u := by
      simpa [hw] using hv
    subst v
    refine ⟨a, ha, ?_⟩
    apply Adj.reachable
    apply M.underlying_adj.mpr
    exact ⟨ULift.up 0, by simp [M, singletonCoverEnds]⟩

private abbrev CycleCoverEdge {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) :=
  p.toSubgraph.spanningCoe.edgeSet

private def IsGoodCycleCoverEdge {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p) : Prop :=
  ∃ a b : S, (e : Sym2 (Option S)) = s(some a, some b) ∧ G.square.Adj a b

private structure BadCycleIncidence {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) where
  edge : CycleCoverEdge p
  vertex : S
  mem_edge : some vertex ∈ (edge : Sym2 (Option S))
  not_good : ¬IsGoodCycleCoverEdge edge

private abbrev NontrivialCoverEdge {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) :=
  {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} ⊕ BadCycleIncidence p

private theorem nontrivialCoverEdgeFinite {S : Set V} [Finite S]
    {p : (G.contractOutside S).square.Walk none none} :
    Finite (NontrivialCoverEdge p) := by
  classical
  let _ := Fintype.ofFinite S
  let f : NontrivialCoverEdge p →
      Sym2 (Option S) ⊕ (Sym2 (Option S) × S)
    | Sum.inl e => Sum.inl e.1.1
    | Sum.inr i => Sum.inr (i.edge.1, i.vertex)
  apply Finite.of_injective f
  intro e e' he
  cases e with
  | inl e =>
      cases e' with
      | inl e' =>
          apply congrArg Sum.inl
          apply Subtype.ext
          apply Subtype.ext
          exact Sum.inl.inj he
      | inr i => contradiction
  | inr i =>
      cases e' with
      | inl e' => contradiction
      | inr i' =>
          cases i with
          | mk ie iv im ib =>
              cases i' with
              | mk je jv jm jb =>
                  have hi : (ie.1, iv) = (je.1, jv) := Sum.inr.inj he
                  have hie : ie = je := Subtype.ext (congrArg Prod.fst hi)
                  subst je
                  have hiv : iv = jv := congrArg Prod.snd hi
                  subst jv
                  rfl

private def NontrivialCoverEdge.sourceCycleEdge {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} :
    NontrivialCoverEdge p → CycleCoverEdge p
  | Sum.inl e => e.1
  | Sum.inr i => i.edge

private noncomputable def goodCycleCoverLeft {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) : S :=
  e.property.choose

private noncomputable def goodCycleCoverRight {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) : S :=
  e.property.choose_spec.choose

private theorem goodCycleCoverEdge_eq {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) :
    (e.1 : Sym2 (Option S)) =
      s(some (goodCycleCoverLeft e), some (goodCycleCoverRight e)) :=
  e.property.choose_spec.choose_spec.1

private theorem goodCycleCoverEdge_adj {S : Set V}
    {p : (G.contractOutside S).square.Walk none none}
    (e : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e}) :
    G.square.Adj (goodCycleCoverLeft e) (goodCycleCoverRight e) :=
  e.property.choose_spec.choose_spec.2

private theorem contractOutside_adj_none_of_strong_cycle_edge {S : Set V}
    [DecidableEq (Option S)]
    {p : (G.contractOutside S).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside S).Adj none p.snd)
    (hlast : (G.contractOutside S).Adj p.penultimate none)
    (d : S) (w : Option S) (he : s(some d, w) ∈ p.edges)
    (hbad : ∀ e, w = some e → ¬G.square.Adj d e) :
    (G.contractOutside S).Adj (some d) none := by
  cases w with
  | none =>
      have he' : s(none, some d) ∈ p.edges := by
        rw [Sym2.eq_swap]
        exact he
      exact (hp.1.property_of_mem_edges_at_start
        ((G.contractOutside S).Adj none ·) hfirst hlast.symm he').symm
  | some e =>
      have hadj : (G.contractOutside S).square.Adj (some d) (some e) :=
        (G.contractOutside S).square.mem_edgeSet.mp (p.edges_subset_edgeSet he)
      exact (Walk.contractOutside_square_adj_some_not_square d e hadj
        (hbad e rfl)).1

private theorem cycleCoverEdge_mem_edges {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p) :
    (e : Sym2 (Option S)) ∈ p.edges := by
  have he := e.property
  change (e : Sym2 (Option S)) ∈ p.toSubgraph.spanningCoe.edgeSet at he
  rw [Subgraph.edgeSet_spanningCoe] at he
  exact p.mem_edges_toSubgraph.mp he

private theorem BadCycleIncidence.exists_attachment [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (i : BadCycleIncidence p) :
    ∃ v ∈ c.support, G.Adj i.vertex v := by
  obtain ⟨w, heq⟩ := Sym2.mem_iff_exists.mp i.mem_edge
  have he : s(some i.vertex, w) ∈ p.edges := by
    rw [← heq]
    exact cycleCoverEdge_mem_edges i.edge
  have hbad : ∀ e, w = some e → ¬G.square.Adj i.vertex e := by
    intro e hwe hadj
    apply i.not_good
    exact ⟨i.vertex, e, heq.trans (congrArg (s(some i.vertex, ·)) hwe), hadj⟩
  have hnone := contractOutside_adj_none_of_strong_cycle_edge hp hfirst hlast
    i.vertex w he hbad
  exact (contractOutside_component_adj_none D i.vertex).mp hnone

private noncomputable def BadCycleIncidence.attachment [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (i : BadCycleIncidence p) : V :=
  (i.exists_attachment D hp hfirst hlast).choose

private theorem BadCycleIncidence.attachment_mem [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (i : BadCycleIncidence p) : i.attachment D hp hfirst hlast ∈ c.support :=
  (i.exists_attachment D hp hfirst hlast).choose_spec.1

private theorem BadCycleIncidence.adj_attachment [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (i : BadCycleIncidence p) : G.Adj i.vertex (i.attachment D hp hfirst hlast) :=
  (i.exists_attachment D hp hfirst hlast).choose_spec.2

private noncomputable def nontrivialCoverEnds [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none) :
    NontrivialCoverEdge p → Sym2 V
  | Sum.inl e => s(goodCycleCoverLeft e, goodCycleCoverRight e)
  | Sum.inr i => s(i.vertex, i.attachment D hp hfirst hlast)

private theorem nontrivialCoverEnds_square_adj [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : NontrivialCoverEdge p) :
    nontrivialCoverEnds D hp hfirst hlast e ∈ G.square.edgeSet := by
  cases e with
  | inl e => exact G.square.mem_edgeSet.mpr (goodCycleCoverEdge_adj e)
  | inr i =>
      have hi := i.adj_attachment D hp hfirst hlast
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hi, Or.inl hi⟩

private noncomputable def nontrivialCoverMultigraph [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none) :
    EdgeIndexedMultigraph V (NontrivialCoverEdge p) where
  ends := nontrivialCoverEnds D hp hfirst hlast
  loopless := by
    intro e v hev
    have hedge := nontrivialCoverEnds_square_adj D hp hfirst hlast e
    rw [hev] at hedge
    exact G.square.loopless.irrefl v (G.square.mem_edgeSet.mp hedge)

private theorem nontrivialCoverEnds_meets_component [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : NontrivialCoverEdge p) :
    ∃ v ∈ c.componentVertices D,
      v ∈ nontrivialCoverEnds D hp hfirst hlast e := by
  cases e with
  | inl e =>
      exact ⟨goodCycleCoverLeft e, (goodCycleCoverLeft e).property,
        Sym2.mem_iff.mpr (Or.inl rfl)⟩
  | inr i =>
      exact ⟨i.vertex, i.vertex.property, Sym2.mem_iff.mpr (Or.inl rfl)⟩

private theorem nontrivialCoverEnds_endpoints_mem [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : NontrivialCoverEdge p) (v : V)
    (hv : v ∈ nontrivialCoverEnds D hp hfirst hlast e) :
    v ∈ c.componentVertices D ∨ v ∈ c.support := by
  cases e with
  | inl e =>
      rcases Sym2.mem_iff.mp hv with hv | hv
      · exact Or.inl (hv.symm ▸ (goodCycleCoverLeft e).property)
      · exact Or.inl (hv.symm ▸ (goodCycleCoverRight e).property)
  | inr i =>
      rcases Sym2.mem_iff.mp hv with hv | hv
      · exact Or.inl (hv.symm ▸ i.vertex.property)
      · exact Or.inr (hv.symm ▸ i.attachment_mem D hp hfirst hlast)

private theorem nontrivialCoverEnds_cycle_edge [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : NontrivialCoverEdge p) (u v : V)
    (he : nontrivialCoverEnds D hp hfirst hlast e = s(u, v))
    (hcycle : u ∈ c.support ∨ v ∈ c.support) : G.Adj u v := by
  cases e with
  | inl e =>
      exfalso
      rcases hcycle with hu | hv
      · have huEnds : u ∈ nontrivialCoverEnds D hp hfirst hlast (Sum.inl e) :=
          he.symm ▸ Sym2.mem_iff.mpr (Or.inl rfl)
        change u ∈ s((goodCycleCoverLeft e : V), (goodCycleCoverRight e : V)) at huEnds
        rcases Sym2.mem_iff.mp huEnds with hlu | hru
        · exact (c.componentVertices_subset_compl D (goodCycleCoverLeft e).property)
            (hlu ▸ hu)
        · exact (c.componentVertices_subset_compl D (goodCycleCoverRight e).property)
            (hru ▸ hu)
      · have hvEnds : v ∈ nontrivialCoverEnds D hp hfirst hlast (Sum.inl e) :=
          he.symm ▸ Sym2.mem_iff.mpr (Or.inr rfl)
        change v ∈ s((goodCycleCoverLeft e : V), (goodCycleCoverRight e : V)) at hvEnds
        rcases Sym2.mem_iff.mp hvEnds with hlv | hrv
        · exact (c.componentVertices_subset_compl D (goodCycleCoverLeft e).property)
            (hlv ▸ hv)
        · exact (c.componentVertices_subset_compl D (goodCycleCoverRight e).property)
            (hrv ▸ hv)
  | inr i =>
      have hi := i.adj_attachment D hp hfirst hlast
      apply G.mem_edgeSet.mp
      rw [← he]
      exact G.mem_edgeSet.mpr hi

private noncomputable def cycleIncidenceToCover [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    (p.toSubgraph.spanningCoe.incidenceSet (some d)) →
      {e : NontrivialCoverEdge p //
        (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} := by
  intro q
  let e : CycleCoverEdge p := ⟨q.1, q.2.1⟩
  by_cases hgood : IsGoodCycleCoverEdge e
  · let g : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} := ⟨e, hgood⟩
    refine ⟨Sum.inl g, ?_⟩
    have hd := q.2.2
    rw [goodCycleCoverEdge_eq g] at hd
    rcases Sym2.mem_iff.mp hd with hd | hd
    · exact Sym2.mem_iff.mpr (Or.inl (congrArg Subtype.val (Option.some.inj hd)))
    · exact Sym2.mem_iff.mpr (Or.inr (congrArg Subtype.val (Option.some.inj hd)))
  · let i : BadCycleIncidence p := ⟨e, d, q.2.2, hgood⟩
    exact ⟨Sum.inr i, Sym2.mem_iff.mpr (Or.inl rfl)⟩

private noncomputable def coverIncidenceToCycle [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    {e : NontrivialCoverEdge p //
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} →
      p.toSubgraph.spanningCoe.incidenceSet (some d) := by
  rintro ⟨e, hde⟩
  cases e with
  | inl e =>
      refine ⟨e.1, e.1.property, ?_⟩
      rw [goodCycleCoverEdge_eq e]
      rcases Sym2.mem_iff.mp hde with hd | hd
      · exact Sym2.mem_iff.mpr (Or.inl (congrArg some (Subtype.ext hd)))
      · exact Sym2.mem_iff.mpr (Or.inr (congrArg some (Subtype.ext hd)))
  | inr i =>
      refine ⟨i.edge.1, i.edge.property, ?_⟩
      rcases Sym2.mem_iff.mp hde with hd | hd
      · have hdi : d = i.vertex := Subtype.ext hd
        exact hdi ▸ i.mem_edge
      · exfalso
        have hd_out := c.componentVertices_subset_compl D d.property
        exact hd_out (hd ▸ i.attachment_mem D hp hfirst hlast)

private theorem cycleIncidenceToCover_source [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : p.toSubgraph.spanningCoe.incidenceSet (some d)) :
    (cycleIncidenceToCover D hp hfirst hlast d q).1.sourceCycleEdge =
      (⟨q.1, q.2.1⟩ : CycleCoverEdge p) := by
  apply Subtype.ext
  simp only [cycleIncidenceToCover]
  split <;> rfl

private theorem coverIncidenceToCycle_val [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : {e : NontrivialCoverEdge p //
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e}) :
    ((coverIncidenceToCycle D hp hfirst hlast d q :
      p.toSubgraph.spanningCoe.incidenceSet (some d)) : Sym2 (Option _)) =
      (q.1.sourceCycleEdge : Sym2 (Option (c.componentVertices D))) := by
  rcases q with ⟨e, he⟩
  cases e <;> rfl

private theorem coverIncidenceToCycle_cycleIncidenceToCover [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : p.toSubgraph.spanningCoe.incidenceSet (some d)) :
    coverIncidenceToCycle D hp hfirst hlast d
      (cycleIncidenceToCover D hp hfirst hlast d q) = q := by
  apply Subtype.ext
  rw [coverIncidenceToCycle_val, cycleIncidenceToCover_source]

private theorem badCycleIncidence_vertex_eq_of_mem [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) (i : BadCycleIncidence p)
    (hde : (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast (Sum.inr i)) :
    d = i.vertex := by
  rcases Sym2.mem_iff.mp hde with hd | hd
  · exact Subtype.ext hd
  · exfalso
    have hd_out := c.componentVertices_subset_compl D d.property
    exact hd_out (hd ▸ i.attachment_mem D hp hfirst hlast)

private theorem cycleIncidenceToCover_coverIncidenceToCycle [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : {e : NontrivialCoverEdge p //
      (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e}) :
    cycleIncidenceToCover D hp hfirst hlast d
      (coverIncidenceToCycle D hp hfirst hlast d q) = q := by
  rcases q with ⟨e, he⟩
  apply Subtype.ext
  cases e with
  | inl g =>
      simp only [coverIncidenceToCycle, cycleIncidenceToCover]
      simp [g.property]
  | inr i =>
      have hdi := badCycleIncidence_vertex_eq_of_mem D hp hfirst hlast d i he
      subst d
      simp only [coverIncidenceToCycle, cycleIncidenceToCover]
      simp [i.not_good]

private noncomputable def cycleCoverIncidenceEquiv [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    p.toSubgraph.spanningCoe.incidenceSet (some d) ≃
      {e : NontrivialCoverEdge p //
        (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} where
  toFun := cycleIncidenceToCover D hp hfirst hlast d
  invFun := coverIncidenceToCycle D hp hfirst hlast d
  left_inv := coverIncidenceToCycle_cycleIncidenceToCover D hp hfirst hlast d
  right_inv := cycleIncidenceToCover_coverIncidenceToCycle D hp hfirst hlast d

private theorem nontrivialCoverMultigraph_degree_eq_two [Finite V]
    [DecidableEq V] {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    (nontrivialCoverMultigraph D hp hfirst hlast).degree d = 2 := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (Option (c.componentVertices D))
  let H := p.toSubgraph.spanningCoe
  have hsubdegree : p.toSubgraph.degree (some d) = 2 := by
    rw [Subgraph.degree, Set.fintypeCard_eq_ncard]
    exact hp.1.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support (some d))
  have hincidence : Nat.card (H.incidenceSet (some d)) = 2 := by
    rw [Nat.card_eq_fintype_card, H.card_incidenceSet_eq_degree]
    change p.toSubgraph.spanningCoe.degree (some d) = 2
    rw [Subgraph.degree_spanningCoe]
    exact hsubdegree
  rw [EdgeIndexedMultigraph.degree, ← Nat.card_coe_set_eq]
  calc
    Nat.card {e : NontrivialCoverEdge p |
        (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} =
        Nat.card (H.incidenceSet (some d)) :=
      Nat.card_congr (cycleCoverIncidenceEquiv D hp hfirst hlast d).symm
    _ = 2 := hincidence

private def cycleCoverEdgeOfMem {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) {a b : Option S}
    (he : s(a, b) ∈ p.edges) : CycleCoverEdge p := by
  refine ⟨s(a, b), ?_⟩
  change s(a, b) ∈ p.toSubgraph.spanningCoe.edgeSet
  rw [Subgraph.edgeSet_spanningCoe, p.mem_edges_toSubgraph]
  exact he

private theorem nontrivialCoverEnds_good_eq [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (e : CycleCoverEdge p) (hgood : IsGoodCycleCoverEdge e)
    (a b : c.componentVertices D) (he : (e : Sym2 _) = s(some a, some b)) :
    nontrivialCoverEnds D hp hfirst hlast
      (Sum.inl (⟨e, hgood⟩ : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e})) =
        s((a : V), (b : V)) := by
  let f : Option (c.componentVertices D) → V := fun z ↦ z.elim a Subtype.val
  have hpair := he.symm.trans (goodCycleCoverEdge_eq ⟨e, hgood⟩)
  have hmapped := congrArg (Sym2.map f) hpair
  simpa [nontrivialCoverEnds, f] using hmapped.symm

private theorem IsGoodCycleCoverEdge.not_of_none_mem {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p)
    (hnone : none ∈ (e : Sym2 (Option S))) : ¬IsGoodCycleCoverEdge e := by
  rintro ⟨a, b, he, _⟩
  rw [he] at hnone
  simp at hnone

private theorem IsGoodCycleCoverEdge.adj_of_eq {S : Set V}
    {p : (G.contractOutside S).square.Walk none none} (e : CycleCoverEdge p)
    (hgood : IsGoodCycleCoverEdge e) (a b : S)
    (he : (e : Sym2 (Option S)) = s(some a, some b)) : G.square.Adj a b := by
  let g : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} := ⟨e, hgood⟩
  let f : Option S → V := fun z ↦ z.elim a Subtype.val
  have hpair := he.symm.trans (goodCycleCoverEdge_eq g)
  have hmapped : s((a : V), (b : V)) =
      s((goodCycleCoverLeft g : V), (goodCycleCoverRight g : V)) := by
    simpa [f] using congrArg (Sym2.map f) hpair
  apply G.square.mem_edgeSet.mp
  rw [hmapped]
  exact G.square.mem_edgeSet.mpr (goodCycleCoverEdge_adj g)

private theorem reachable_cycle_of_cycle_subwalk [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D)
    (q : (G.contractOutside (c.componentVertices D)).square.Walk (some d) none)
    (hq : ∀ e ∈ q.edges, e ∈ p.edges) :
    ∃ w ∈ c.support,
      (nontrivialCoverMultigraph D hp hfirst hlast).underlying.Reachable d w := by
  cases hqdef : q with
  | @cons _ z _ hz q' =>
      have hedge_mem : s(some d, z) ∈ p.edges := by
        apply hq
        rw [hqdef, SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self
      let e : CycleCoverEdge p := cycleCoverEdgeOfMem p hedge_mem
      cases z with
      | none =>
          have hnone : none ∈ (e : Sym2 (Option (c.componentVertices D))) := by
            exact Sym2.mem_iff.mpr (Or.inr rfl)
          let i : BadCycleIncidence p :=
            ⟨e, d, Sym2.mem_iff.mpr (Or.inl rfl),
              IsGoodCycleCoverEdge.not_of_none_mem e hnone⟩
          refine ⟨i.attachment D hp hfirst hlast,
            i.attachment_mem D hp hfirst hlast, ?_⟩
          apply Adj.reachable
          apply (nontrivialCoverMultigraph D hp hfirst hlast).underlying_adj.mpr
          exact ⟨Sum.inr i, rfl⟩
      | some d' =>
          by_cases hgood : G.square.Adj d d'
          · have heq : (e : Sym2 (Option (c.componentVertices D))) =
                s(some d, some d') := rfl
            have hgood_edge : IsGoodCycleCoverEdge e := ⟨d, d', heq, hgood⟩
            let g : {e : CycleCoverEdge p // IsGoodCycleCoverEdge e} :=
              ⟨e, hgood_edge⟩
            have hadj : (nontrivialCoverMultigraph D hp hfirst hlast).underlying.Adj d d' := by
              apply (nontrivialCoverMultigraph D hp hfirst hlast).underlying_adj.mpr
              exact ⟨Sum.inl g,
                nontrivialCoverEnds_good_eq D hp hfirst hlast e hgood_edge d d' heq⟩
            have htail : ∀ f ∈ q'.edges, f ∈ p.edges := by
              intro f hf
              apply hq f
              rw [hqdef, SimpleGraph.Walk.edges_cons]
              exact List.mem_cons_of_mem _ hf
            obtain ⟨w, hwc, hw⟩ :=
              reachable_cycle_of_cycle_subwalk D hp hfirst hlast d' q' htail
            exact ⟨w, hwc, hadj.reachable.trans hw⟩
          · have hnot_good : ¬IsGoodCycleCoverEdge e := by
              intro h
              exact hgood (IsGoodCycleCoverEdge.adj_of_eq e h d d' rfl)
            let i : BadCycleIncidence p :=
              ⟨e, d, Sym2.mem_iff.mpr (Or.inl rfl), hnot_good⟩
            refine ⟨i.attachment D hp hfirst hlast,
              i.attachment_mem D hp hfirst hlast, ?_⟩
            apply Adj.reachable
            apply (nontrivialCoverMultigraph D hp hfirst hlast).underlying_adj.mpr
            exact ⟨Sum.inr i, rfl⟩
termination_by q.length
decreasing_by
  rw [hqdef, SimpleGraph.Walk.length_cons]
  omega

private theorem nontrivialCoverMultigraph_reachable_cycle [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    ∃ w ∈ c.support,
      (nontrivialCoverMultigraph D hp hfirst hlast).underlying.Reachable d w := by
  let r := p.rotate (some d) (hp.mem_support (some d))
  have hnone : none ∈ r.support := by
    rw [p.mem_support_rotate_iff]
    exact hp.mem_support none
  let q := r.takeUntil none hnone
  have hq : ∀ e ∈ q.edges, e ∈ p.edges := by
    intro e he
    have her : e ∈ r.edges := r.edges_takeUntil_subset_edges hnone he
    exact (p.rotate_edges (some d) (hp.mem_support (some d))).mem_iff.mp her
  exact reachable_cycle_of_cycle_subwalk D hp hfirst hlast d q hq

/-- A strong Hamiltonian cycle in a nontrivial component contraction yields the Step A trail
cover for that component. -/
private theorem ComponentTrailCover.exists_of_contractOutside_strongCycle
    [Finite V] [DecidableEq V] {c : G.Walk x x}
    (D : c.outsideGraph.ConnectedComponent) [Fintype (c.componentVertices D)]
    (hstrong : (G.contractOutside (c.componentVertices D)).HasStrongSquareCycle none) :
    Nonempty (c.ComponentTrailCover D) := by
  classical
  obtain ⟨p, hp, hfirst, hlast⟩ := hstrong
  let M := nontrivialCoverMultigraph D hp hfirst hlast
  refine ⟨{
    Edge := NontrivialCoverEdge p
    edge_finite := nontrivialCoverEdgeFinite
    multigraph := M
    square_adj := nontrivialCoverEnds_square_adj D hp hfirst hlast
    meets_component := nontrivialCoverEnds_meets_component D hp hfirst hlast
    endpoints_mem := nontrivialCoverEnds_endpoints_mem D hp hfirst hlast
    cycle_edge := nontrivialCoverEnds_cycle_edge D hp hfirst hlast
    degree_eq_two := ?_
    reachable_cycle := ?_ }⟩
  · intro v hv
    let d : c.componentVertices D := ⟨v, hv⟩
    exact nontrivialCoverMultigraph_degree_eq_two D hp hfirst hlast d
  · intro v hv
    let d : c.componentVertices D := ⟨v, hv⟩
    exact nontrivialCoverMultigraph_reachable_cycle D hp hfirst hlast d

end Walk

end SimpleGraph

/-! ## CycleTrailSystem -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- Edge identities in the union of a cycle and one trail cover for every outside component. -/
private abbrev TrailSystemEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :=
  ULift.{u} (Fin c.length) ⊕ Σ D, (cover D).Edge

private instance trailSystemEdgeFinite [Finite V] (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    Finite (c.TrailSystemEdge cover) := by
  let _ : ∀ D : c.outsideGraph.ConnectedComponent, Finite (cover D).Edge :=
    fun D ↦ (cover D).edge_finite
  infer_instance

/-- The indexed multigraph formed by the cycle and all outside-component trail covers. -/
private noncomputable def trailSystemMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    EdgeIndexedMultigraph V (c.TrailSystemEdge cover) where
  ends
    | Sum.inl i => s(c.getVert i.down, c.getVert (i.down + 1))
    | Sum.inr e => (cover e.1).multigraph.ends e.2
  loopless := by
    intro e v he
    cases e with
    | inl i =>
        have hadj := c.adj_getVert_succ i.down.isLt
        have hedge : s(c.getVert i.down, c.getVert (i.down + 1)) ∈ G.edgeSet :=
          G.mem_edgeSet.mpr hadj
        change s(c.getVert i.down, c.getVert (i.down + 1)) = s(v, v) at he
        rw [he] at hedge
        exact G.loopless.irrefl v (G.mem_edgeSet.mp hedge)
    | inr e => exact (cover e.1).multigraph.loopless e.2 v he

/-- Every trail-system edge is an edge of the square. -/
private theorem trailSystemMultigraph_square_adj
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (e : c.TrailSystemEdge cover) :
    (c.trailSystemMultigraph cover).ends e ∈ G.square.edgeSet := by
  cases e with
  | inl i =>
      have h := c.adj_getVert_succ i.down.isLt
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj h, Or.inl h⟩
  | inr e => exact (cover e.1).square_adj e.2

/-- Every trail-system edge incident with the cycle is an original graph edge. -/
private theorem trailSystemMultigraph_cycle_edge
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (e : c.TrailSystemEdge cover) (u v : V)
    (he : (c.trailSystemMultigraph cover).ends e = s(u, v))
    (hcycle : u ∈ c.support ∨ v ∈ c.support) : G.Adj u v := by
  cases e with
  | inl i =>
      apply G.mem_edgeSet.mp
      rw [← he]
      exact G.mem_edgeSet.mpr (c.adj_getVert_succ i.down.isLt)
  | inr e => exact (cover e.1).cycle_edge e.2 u v he hcycle

/-- A graph is connected when its cycle vertices reach the root and every outside component
cover maps into it. -/
private theorem connected_of_cycle_reachable_and_component_covers
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (H : SimpleGraph V)
    (hcycle : ∀ v, v ∈ c.support → H.Reachable v x)
    (hcover : ∀ D, (cover D).multigraph.underlying →g H)
    (hcover_id : ∀ D v, hcover D v = v) : H.Connected := by
  refine { preconnected := ?_, nonempty := ⟨x⟩ }
  intro u v
  suffices ∀ w, H.Reachable w x by
    exact (this u).trans (this v).symm
  intro w
  by_cases hw : w ∈ c.support
  · exact hcycle w hw
  · let w' : {z : V // z ∉ c.support} := ⟨w, hw⟩
    let D := c.outsideGraph.connectedComponentMk w'
    have hwD : w ∈ c.componentVertices D := by
      apply (c.mem_componentVertices_iff D w).mpr
      exact ⟨hw, ConnectedComponent.connectedComponentMk_mem⟩
    obtain ⟨z, hzc, hwz⟩ := (cover D).reachable_cycle w hwD
    have hwz' : H.Reachable w z := by
      simpa only [hcover_id] using hwz.map (hcover D)
    exact hwz'.trans (hcycle z hzc)

private def outsideComponent (c : G.Walk x x) {v : V} (hv : v ∉ c.support) :
    c.outsideGraph.ConnectedComponent :=
  c.outsideGraph.connectedComponentMk ⟨v, hv⟩

private theorem mem_componentVertices_outsideComponent (c : G.Walk x x)
    {v : V} (hv : v ∉ c.support) :
    v ∈ c.componentVertices (outsideComponent c hv) := by
  apply (c.mem_componentVertices_iff (outsideComponent c hv) v).mpr
  exact ⟨hv, ConnectedComponent.connectedComponentMk_mem⟩

private theorem component_eq_outsideComponent (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) {v : V} (hv : v ∉ c.support)
    (hvD : v ∈ c.componentVertices D) : outsideComponent c hv = D := by
  obtain ⟨hv', hD⟩ := (c.mem_componentVertices_iff D v).mp hvD
  simpa [outsideComponent] using hD

private theorem mem_support_of_mem_cycle_edge (c : G.Walk x x)
    (i : Fin c.length) {v : V}
    (hv : v ∈ s(c.getVert i, c.getVert (i + 1))) : v ∈ c.support := by
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact c.getVert_mem_support i
  · exact c.getVert_mem_support (i + 1)

private def componentIncidenceToTrailSystem (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : (cover (outsideComponent c hv)).Edge |
      (cover (outsideComponent c hv)).multigraph.Inc v e} →
      {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} :=
  fun e ↦ ⟨Sum.inr ⟨outsideComponent c hv, e.1⟩, e.2⟩

private noncomputable def trailSystemIncidenceToComponent (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} →
      {e : (cover (outsideComponent c hv)).Edge |
        (cover (outsideComponent c hv)).multigraph.Inc v e} := by
  rintro ⟨e, hve⟩
  cases e with
  | inl i =>
      exfalso
      exact hv (mem_support_of_mem_cycle_edge c i.down hve)
  | inr e =>
      rcases e with ⟨D, e⟩
      have hvD : v ∈ c.componentVertices D := by
        rcases (cover D).endpoints_mem e v hve with hvD | hvc
        · exact hvD
        · exact False.elim (hv hvc)
      have hD := component_eq_outsideComponent c D hv hvD
      subst D
      exact ⟨e, hve⟩

private noncomputable def trailSystemIncidenceEquiv (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : (cover (outsideComponent c hv)).Edge |
      (cover (outsideComponent c hv)).multigraph.Inc v e} ≃
      {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} where
  toFun := componentIncidenceToTrailSystem c cover hv
  invFun := trailSystemIncidenceToComponent c cover hv
  left_inv := by
    intro e
    apply Subtype.ext
    simp [componentIncidenceToTrailSystem, trailSystemIncidenceToComponent]
  right_inv := by
    rintro ⟨e, he⟩
    apply Subtype.ext
    cases e with
    | inl i => exact False.elim (hv (mem_support_of_mem_cycle_edge c i.down he))
    | inr e =>
        rcases e with ⟨D, e⟩
        have hvD : v ∈ c.componentVertices D := by
          rcases (cover D).endpoints_mem e v he with hvD | hvc
          · exact hvD
          · exact False.elim (hv hvc)
        have hD := component_eq_outsideComponent c D hv hvD
        subst D
        rfl

/-- Every vertex outside the cycle has degree two in the Step A trail system. -/
private theorem trailSystemMultigraph_degree_eq_two [Finite V] (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    (c.trailSystemMultigraph cover).degree v = 2 := by
  let D := outsideComponent c hv
  calc
    (c.trailSystemMultigraph cover).degree v =
        Nat.card {e : c.TrailSystemEdge cover |
          (c.trailSystemMultigraph cover).Inc v e} := by
      rw [EdgeIndexedMultigraph.degree, Nat.card_coe_set_eq]
    _ = Nat.card {e : (cover D).Edge | (cover D).multigraph.Inc v e} :=
      Nat.card_congr (trailSystemIncidenceEquiv c cover hv).symm
    _ = (cover D).multigraph.degree v := by
      rw [EdgeIndexedMultigraph.degree, Nat.card_coe_set_eq]
    _ = 2 := (cover D).degree_eq_two v (mem_componentVertices_outsideComponent c hv)

/-- The sum of the trail-system degrees around the cycle is even. -/
private theorem trailSystemMultigraph_cycle_degree_sum_even [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    Even (∑ i : Fin c.length,
      (c.trailSystemMultigraph cover).degree (c.getVert i)) := by
  classical
  let _ := Fintype.ofFinite V
  let M := c.trailSystemMultigraph cover
  have htotal : Even (∑ v : V, M.degree v) := M.even_sum_degree
  let cycleVertices : Finset V := Finset.univ.filter fun v ↦ v ∈ c.support
  let outsideVertices : Finset V := Finset.univ.filter fun v ↦ v ∉ c.support
  have hsplit : (∑ v ∈ cycleVertices, M.degree v) +
      (∑ v ∈ outsideVertices, M.degree v) = ∑ v : V, M.degree v := by
    simpa [cycleVertices, outsideVertices] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun v : V ↦ v ∈ c.support) (fun v ↦ M.degree v)
  rw [← hsplit] at htotal
  have hout : Even (∑ v ∈ outsideVertices, M.degree v) := by
    have heq : (∑ v ∈ outsideVertices, M.degree v) =
        ∑ _v ∈ outsideVertices, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      apply c.trailSystemMultigraph_degree_eq_two cover
      simpa [outsideVertices] using hv
    rw [heq]
    exact ⟨outsideVertices.card, by simp; omega⟩
  have hsupport : Even (∑ v ∈ cycleVertices, M.degree v) :=
    (Nat.even_add.mp htotal).mpr hout
  have hsum : (∑ i : Fin c.length, M.degree (c.getVert i)) =
      ∑ v ∈ cycleVertices, M.degree v := by
    refine Finset.sum_bij (s := (Finset.univ : Finset (Fin c.length)))
      (t := cycleVertices) (fun i _ ↦ c.getVert i) ?_ ?_ ?_ ?_
    · intro i _
      simp [cycleVertices]
    · intro i _ j _ hij
      apply hc.finLengthEquivSupport.injective
      apply Subtype.ext
      simpa using hij
    · intro v hv
      have hvc : v ∈ c.support := by simpa [cycleVertices] using hv
      let v' : {z : V // z ∈ c.support} := ⟨v, hvc⟩
      let i := hc.finLengthEquivSupport.symm v'
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply (hc.finLengthEquivSupport_apply i).symm.trans
      simpa only [i, v'] using
        congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply v')
    · intro i _
      rfl
  rw [hsum]
  exact hsupport

end Walk

end SimpleGraph

/-! ## CycleParity -/


open scoped BigOperators

/-- A choice of at most one copied edge at every position of a cyclic degree sequence. -/
private structure CyclicParityCompletion {n : ℕ} [NeZero n] (d : Fin n → ℕ) where
  /-- The number of extra copies, always zero or one. -/
  copies : Fin n → ℕ
  copies_lt_two : ∀ i, copies i < 2
  /-- Position zero is the protected edge. -/
  copies_zero : copies 0 = 0
  /-- The two incident copy choices correct the parity at each cyclic vertex. -/
  even_at : ∀ i, Even (d i + copies (i - 1) + copies i)

/-- Sum of the degrees strictly after position zero and at most position `i`. -/
private def cyclicPrefix {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∑ j : Fin i.val,
    d ⟨j.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt j.isLt) i.isLt⟩

private theorem cyclicPrefix_zero {n : ℕ} [NeZero n] (d : Fin n → ℕ) :
    cyclicPrefix d 0 = 0 := by
  simp [cyclicPrefix]

private theorem cyclicPrefix_eq_sub_one_add {n : ℕ} [NeZero n]
    (d : Fin n → ℕ) (i : Fin n) (hi : i ≠ 0) :
    cyclicPrefix d i = cyclicPrefix d (i - 1) + d i := by
  rcases i with ⟨i, hiLt⟩
  cases i with
  | zero => exact (hi rfl).elim
  | succ k =>
      let p : Fin n := ⟨k, lt_trans (Nat.lt_succ_self k) hiLt⟩
      have hp : (⟨k + 1, hiLt⟩ - 1 : Fin n) = p := by
        apply Fin.ext
        rw [Fin.val_sub_one_of_ne_zero hi]
        change k + 1 - 1 = k
        omega
      rw [hp]
      simp only [cyclicPrefix, p, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

private theorem zero_add_cyclicPrefix_last {m : ℕ} (d : Fin (m + 1) → ℕ) :
    d 0 + cyclicPrefix d (Fin.last m) = ∑ i, d i := by
  rw [Fin.sum_univ_succ]
  simp only [cyclicPrefix, Fin.val_last]
  congr

/-- The canonical parity completion, obtained by taking prefix parities away from position
zero. -/
private noncomputable def cyclicParityCompletion {n : ℕ} [NeZero n]
    (d : Fin n → ℕ) (hsum : Even (∑ i, d i)) : CyclicParityCompletion d where
  copies i := cyclicPrefix d i % 2
  copies_lt_two i := Nat.mod_lt _ (by omega)
  copies_zero := by simp [cyclicPrefix_zero]
  even_at := by
    intro i
    by_cases hi : i = 0
    · subst i
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      have hprev : (0 - 1 : Fin (m + 1)) = Fin.last m := by
        cases m with
        | zero =>
            apply Fin.ext
            rfl
        | succ k =>
            apply Fin.ext
            simp
      rw [hprev, cyclicPrefix_zero]
      rw [← zero_add_cyclicPrefix_last d] at hsum
      rw [Nat.even_iff] at hsum ⊢
      omega
    · rw [cyclicPrefix_eq_sub_one_add d i hi, Nat.even_iff]
      omega

/-! ## CycleCopies -/


namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- Edge identities for prescribed copies of edges of a closed walk. -/
private abbrev CycleCopyEdge (c : G.Walk x x) [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :=
  Σ i : Fin c.length, Fin (q.copies i)

private instance cycleCopyEdgeFinite (c : G.Walk x x) [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    Finite (c.CycleCopyEdge q) := by
  infer_instance

/-- The indexed multigraph of the prescribed parallel cycle-edge copies. -/
private def cycleCopyMultigraph (c : G.Walk x x) [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    EdgeIndexedMultigraph V (c.CycleCopyEdge q) where
  ends e := s(c.getVert e.1, c.getVert (e.1.val + 1))
  loopless := by
    intro e v he
    have hadj := c.adj_getVert_succ e.1.isLt
    apply G.loopless.irrefl v
    apply G.mem_edgeSet.mp
    rw [← he]
    exact G.mem_edgeSet.mpr hadj

private theorem IsCycle.getVert_injective_fin {c : G.Walk x x} (hc : c.IsCycle) :
    Function.Injective (fun i : Fin c.length ↦ c.getVert i) := by
  intro i j hij
  apply hc.finLengthEquivSupport.injective
  apply Subtype.ext
  simpa using hij

private theorem IsCycle.getVert_succ_eq_add_one {c : G.Walk x x} (hc : c.IsCycle)
    [NeZero c.length] (i : Fin c.length) :
    c.getVert (i.val + 1) = c.getVert (i + 1 : Fin c.length) := by
  have hlength : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
  have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt hlength
  by_cases hlt : i.val + 1 < c.length
  · have hval : (i + 1 : Fin c.length).val = i.val + 1 := by
      have haddlt : i.val + (1 : Fin c.length).val < c.length := by
        rw [hone]
        exact hlt
      rw [Fin.val_add_eq_of_add_lt haddlt, hone]
    rw [hval]
  · have heq : i.val + 1 = c.length := by omega
    have hzero : (i + 1 : Fin c.length) = 0 := by
      apply Fin.ext
      simp [Fin.val_add, heq]
    rw [heq, c.getVert_length, hzero]
    change x = c.getVert 0
    exact c.getVert_zero.symm

private theorem cycleCopyMultigraph_inc_getVert_iff {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) (e : c.CycleCopyEdge q) :
    (c.cycleCopyMultigraph q).Inc (c.getVert i) e ↔
      e.1 = i ∨ e.1 = i - 1 := by
  change c.getVert i ∈ s(c.getVert e.1, c.getVert (e.1.val + 1)) ↔ _
  rw [hc.getVert_succ_eq_add_one]
  constructor
  · intro he
    rcases Sym2.mem_iff.mp he with he | he
    · exact Or.inl (hc.getVert_injective_fin he.symm)
    · have hi : i = e.1 + 1 := hc.getVert_injective_fin he
      exact Or.inr (eq_sub_iff_add_eq.mpr hi.symm)
  · rintro (rfl | he)
    · exact Sym2.mem_iff.mpr (Or.inl rfl)
    · apply Sym2.mem_iff.mpr
      right
      apply congrArg c.getVert
      rw [he, sub_add_cancel]

private theorem IsCycle.sub_one_ne {c : G.Walk x x} (hc : c.IsCycle)
    [NeZero c.length] (i : Fin c.length) : i - 1 ≠ i := by
  intro hi
  have hadd := congrArg (fun z : Fin c.length ↦ z + 1) hi
  rw [sub_add_cancel] at hadd
  have hzero : (0 : Fin c.length) = 1 := by
    apply add_left_cancel (a := i)
    simpa using hadd
  have hlength : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
  have hval := congrArg (fun z : Fin c.length ↦ z.val) hzero
  simp at hval
  omega

private theorem no_cover_inc_bound_vertex [Finite V] (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i))
    (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge) :
    ¬(c.trailSystemMultigraph cover).Inc (c.getVert i) (Sum.inr ⟨D, f⟩) := by
  intro hinc
  obtain ⟨z, hzD, hzinc⟩ := (cover D).meets_component f
  have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
  have hne : c.getVert i ≠ z := by
    intro h
    exact hzout (h ▸ c.getVert_mem_support i)
  change c.getVert i ∈ (cover D).multigraph.ends f at hinc
  have hends : (cover D).multigraph.ends f = s(c.getVert i, z) :=
    (Sym2.mem_and_mem_iff hne).mp ⟨hinc, hzinc⟩
  have hadj : G.Adj (c.getVert i) z :=
    (cover D).cycle_edge f _ _ hends (Or.inl (c.getVert_mem_support i))
  exact hzout (hbound.2 hadj)

private noncomputable def boundIncidenceEquiv [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i)) :
    {e : c.TrailSystemEdge cover //
      (c.trailSystemMultigraph cover).Inc (c.getVert i) e} ≃ Fin 2 := by
  let embed : Fin 2 → {e : c.TrailSystemEdge cover //
      (c.trailSystemMultigraph cover).Inc (c.getVert i) e} := fun k ↦
    if hk : k = 0 then
      ⟨Sum.inl (ULift.up i), by
        change c.getVert i ∈ s(c.getVert i, c.getVert (i + 1))
        simp⟩
    else
      ⟨Sum.inl (ULift.up (i - 1)), by
        simp only [EdgeIndexedMultigraph.Inc, trailSystemMultigraph]
        rw [hc.getVert_succ_eq_add_one, sub_add_cancel]
        exact Sym2.mem_iff.mpr (Or.inr rfl)⟩
  have hinj : Function.Injective embed := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · exact hb.symm
      · have hval := congrArg (fun e ↦ e.1) hab
        simp only [embed, dite_eq_left rfl, dite_eq_right hb] at hval
        have hindex : i = i - 1 := by
          simpa only [Sum.inl.injEq, ULift.up_inj] using hval
        exact False.elim (hc.sub_one_ne i hindex.symm)
    · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
      subst a
      by_cases hb : b = 0
      · subst b
        have hval := congrArg (fun e ↦ e.1) hab
        simp only [embed, dite_eq_left rfl,
          dite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hval
        have hindex : i - 1 = i := by
          simpa only [Sum.inl.injEq, ULift.up_inj] using hval
        exact False.elim (hc.sub_one_ne i hindex)
      · exact (Fin.eq_one_of_ne_zero b hb).symm
  have hsurj : Function.Surjective embed := by
    rintro ⟨e, he⟩
    cases e with
    | inr e =>
        exact False.elim
          (no_cover_inc_bound_vertex c cover i hbound e.1 e.2 he)
    | inl j =>
        change c.getVert i ∈
          s(c.getVert j.down, c.getVert (j.down + 1)) at he
        rcases Sym2.mem_iff.mp he with he | he
        · have hji : j.down = i := hc.getVert_injective_fin he.symm
          refine ⟨0, ?_⟩
          apply Subtype.ext
          change Sum.inl (ULift.up i) = Sum.inl j
          congr
          exact hji.symm
        · rw [hc.getVert_succ_eq_add_one] at he
          have hi : i = j.down + 1 := hc.getVert_injective_fin he
          have hji : j.down = i - 1 := eq_sub_iff_add_eq.mpr hi.symm
          refine ⟨1, ?_⟩
          apply Subtype.ext
          change Sum.inl (ULift.up (i - 1)) = Sum.inl j
          congr
          exact hji.symm
  exact (Equiv.ofBijective embed ⟨hinj, hsurj⟩).symm

/-- A bound cycle vertex is incident only with the two cycle edges in the Step A trail
system. -/
private theorem trailSystemMultigraph_degree_eq_two_of_isBoundVertex [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i)) :
    (c.trailSystemMultigraph cover).degree (c.getVert i) = 2 := by
  calc
    (c.trailSystemMultigraph cover).degree (c.getVert i) =
        Nat.card {e : c.TrailSystemEdge cover //
          (c.trailSystemMultigraph cover).Inc (c.getVert i) e} := by
      exact (Nat.card_coe_set_eq
        {e : c.TrailSystemEdge cover |
          (c.trailSystemMultigraph cover).Inc (c.getVert i) e}).symm
    _ = Nat.card (Fin 2) := Nat.card_congr (boundIncidenceEquiv c hc cover i hbound)
    _ = 2 := Nat.card_fin 2

private noncomputable def cycleCopyIncidenceTo {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e} →
      Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) := by
  rintro ⟨⟨j, k⟩, he⟩
  by_cases hji : j = i
  · subst j
    exact Sum.inr k
  · have hjp : j = i - 1 :=
      (cycleCopyMultigraph_inc_getVert_iff hc q i ⟨j, k⟩).mp he |>.resolve_left hji
    subst j
    exact Sum.inl k

private def cycleCopyIncidenceFrom {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) →
      {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e}
  | Sum.inl k =>
      ⟨⟨i - 1, k⟩, (cycleCopyMultigraph_inc_getVert_iff hc q i _).mpr (Or.inr rfl)⟩
  | Sum.inr k =>
      ⟨⟨i, k⟩, (cycleCopyMultigraph_inc_getVert_iff hc q i _).mpr (Or.inl rfl)⟩

private theorem cycleCopyIncidence_leftInverse {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Function.LeftInverse (cycleCopyIncidenceFrom hc q i)
      (cycleCopyIncidenceTo hc q i) := by
  rintro ⟨⟨j, k⟩, he⟩
  by_cases hji : j = i
  · subst j
    simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom]
  · have hjp : j = i - 1 :=
      (cycleCopyMultigraph_inc_getVert_iff hc q i ⟨j, k⟩).mp he |>.resolve_left hji
    subst j
    simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom, hc.sub_one_ne i]

private theorem cycleCopyIncidence_rightInverse {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Function.RightInverse (cycleCopyIncidenceFrom hc q i)
      (cycleCopyIncidenceTo hc q i) := by
  intro e
  cases e with
  | inl k =>
      simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom, hc.sub_one_ne i]
  | inr k =>
      simp [cycleCopyIncidenceTo, cycleCopyIncidenceFrom]

private noncomputable def cycleCopyIncidenceEquiv {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e} ≃
      Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) where
  toFun := cycleCopyIncidenceTo hc q i
  invFun := cycleCopyIncidenceFrom hc q i
  left_inv := cycleCopyIncidence_leftInverse hc q i
  right_inv := cycleCopyIncidence_rightInverse hc q i

/-- At a cycle vertex, copied-edge degree is the sum of the copy counts on its two incident
edges. -/
private theorem cycleCopyMultigraph_degree_getVert {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    (c.cycleCopyMultigraph q).degree (c.getVert i) =
      q.copies (i - 1) + q.copies i := by
  calc
    (c.cycleCopyMultigraph q).degree (c.getVert i) =
        Nat.card {e : c.CycleCopyEdge q //
          (c.cycleCopyMultigraph q).Inc (c.getVert i) e} := by
      rw [EdgeIndexedMultigraph.degree]
      exact (Nat.card_coe_set_eq
        {e : c.CycleCopyEdge q |
          (c.cycleCopyMultigraph q).Inc (c.getVert i) e}).symm
    _ = Nat.card (Fin (q.copies (i - 1)) ⊕ Fin (q.copies i)) :=
      Nat.card_congr (cycleCopyIncidenceEquiv hc q i)
    _ = Nat.card (Fin (q.copies (i - 1))) + Nat.card (Fin (q.copies i)) :=
      Nat.card_sum
    _ = q.copies (i - 1) + q.copies i := by
      rw [Nat.card_fin, Nat.card_fin]

/-- A copied cycle edge is an edge of the original graph. -/
private theorem cycleCopyMultigraph_mem_edgeSet (c : G.Walk x x)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (e : c.CycleCopyEdge q) :
    (c.cycleCopyMultigraph q).ends e ∈ G.edgeSet := by
  exact G.mem_edgeSet.mpr (c.adj_getVert_succ e.1.isLt)

/-- Vertices outside the cycle have copied-edge degree zero. -/
private theorem cycleCopyMultigraph_degree_eq_zero_of_not_mem {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) {v : V} (hv : v ∉ c.support) :
    (c.cycleCopyMultigraph q).degree v = 0 := by
  rw [EdgeIndexedMultigraph.degree, Set.ncard_eq_zero]
  ext e
  rw [Set.mem_empty_iff_false, iff_false]
  intro he
  rcases e with ⟨i, k⟩
  change v ∈ s(c.getVert i, c.getVert (i.val + 1)) at he
  rcases Sym2.mem_iff.mp he with rfl | rfl
  · exact hv (c.getVert_mem_support i)
  · apply hv
    rw [hc.getVert_succ_eq_add_one]
    exact c.getVert_mem_support (i + 1 : Fin c.length)

end Walk

end SimpleGraph

/-! ## CycleEulerization -/


namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- The canonical copy choices that correct the trail-system degrees on a cycle. -/
private noncomputable def cycleEulerizationCompletion [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    CyclicParityCompletion
      (fun i : Fin c.length ↦ (c.trailSystemMultigraph cover).degree (c.getVert i)) :=
  cyclicParityCompletion _ (c.trailSystemMultigraph_cycle_degree_sum_even hc cover)

/-- The Step A trail system together with its parity-correcting cycle-edge copies. -/
private noncomputable def cycleEulerizationMultigraph [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :=
  (c.trailSystemMultigraph cover).disjointSum
    (c.cycleCopyMultigraph (c.cycleEulerizationCompletion hc cover))

/-- Every vertex has even degree after parity correction. -/
private theorem cycleEulerization_even_degree [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (v : V) : Even (c.cycleEulerizationMultigraph hc cover |>.degree v) := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  rw [cycleEulerizationMultigraph, EdgeIndexedMultigraph.disjointSum_degree]
  by_cases hv : v ∈ c.support
  · let v' : {z : V // z ∈ c.support} := ⟨v, hv⟩
    let i := hc.finLengthEquivSupport.symm v'
    have hvi : c.getVert i = v := by
      apply (hc.finLengthEquivSupport_apply i).symm.trans
      simpa only [i, v'] using
        congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply v')
    rw [← hvi, c.cycleCopyMultigraph_degree_getVert hc]
    change Even ((c.trailSystemMultigraph cover).degree (c.getVert i) +
      (q.copies (i - 1) + q.copies i))
    simpa only [Nat.add_assoc] using q.even_at i
  · rw [c.trailSystemMultigraph_degree_eq_two cover hv,
      c.cycleCopyMultigraph_degree_eq_zero_of_not_mem hc _ hv]
    exact even_two

end Walk

end SimpleGraph

/-! ## TransitionCompression -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- Two adjacent indexed edges to be traversed consecutively. -/
private structure EdgeTransition where
  /-- First edge of the pass. -/
  left : E
  /-- Second edge of the pass. -/
  right : E
  /-- Outer endpoint of the first edge. -/
  before : V
  /-- Common endpoint. -/
  center : V
  /-- Outer endpoint of the second edge. -/
  after : V
  left_ends : M.ends left = s(before, center)
  right_ends : M.ends right = s(center, after)
  before_ne_after : before ≠ after

/-- Select one of the two original edge identities belonging to a transition. -/
private def transitionEdge {T : Type*} (transition : T → M.EdgeTransition) :
    T × Fin 2 → E
  | (t, side) => if side = 0 then (transition t).left else (transition t).right

/-- Original edges not consumed by a forced transition. -/
private abbrev UnpairedTransitionEdge {T : Type*}
    (transition : T → M.EdgeTransition) :=
  {e : E // e ∉ Set.range (M.transitionEdge transition)}

/-- Edge identities after every forced transition is compressed to one temporary edge. -/
private abbrev CompressedTransitionEdge {T : Type*}
    (transition : T → M.EdgeTransition) :=
  M.UnpairedTransitionEdge transition ⊕ T

private instance unpairedTransitionEdgeFinite {T : Type*} [Finite E]
    (transition : T → M.EdgeTransition) :
    Finite (M.UnpairedTransitionEdge transition) :=
  inferInstance

private instance compressedTransitionEdgeFinite {T : Type*} [Finite E] [Finite T]
    (transition : T → M.EdgeTransition) :
    Finite (M.CompressedTransitionEdge transition) :=
  inferInstance

/-- Simultaneously compress a family of forced transitions. -/
private def compressTransitions {T : Type*} (transition : T → M.EdgeTransition) :
    EdgeIndexedMultigraph V (M.CompressedTransitionEdge transition) where
  ends
    | Sum.inl e => M.ends e.1
    | Sum.inr t => s((transition t).before, (transition t).after)
  loopless := by
    intro e v he
    cases e with
    | inl e => exact M.loopless e.1 v he
    | inr t =>
        rcases Sym2.eq_iff.mp he with h | h
        · exact (transition t).before_ne_after (h.1.trans h.2.symm)
        · exact (transition t).before_ne_after (h.1.trans h.2.symm)

private theorem degree_eq_sum_incidence [Fintype E] (v : V)
    [DecidablePred (M.Inc v)] :
    M.degree v = ∑ e : E, if M.Inc v e then 1 else 0 := by
  unfold degree
  have hset : {e : E | M.Inc v e} =
      (Finset.univ.filter (M.Inc v) : Finset E) := by
    ext e
    simp
  rw [hset, Set.ncard_coe_finset, Finset.sum_boole]
  congr 1

private noncomputable def edgePartitionEquiv {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) :
    E ≃ M.UnpairedTransitionEdge transition ⊕ (T × Fin 2) := by
  classical
  exact
    (Equiv.sumCompl (fun e ↦ e ∈ Set.range (M.transitionEdge transition))).symm |>.trans
      (Equiv.sumCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl _)) |>.trans
      (Equiv.sumComm _ _)

@[simp]
private theorem edgePartitionEquiv_symm_apply_inl {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition))
    (e : M.UnpairedTransitionEdge transition) :
    (M.edgePartitionEquiv transition hinj).symm (Sum.inl e) = e.1 := by
  simp [edgePartitionEquiv]

@[simp]
private theorem edgePartitionEquiv_symm_apply_inr {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (p : T × Fin 2) :
    (M.edgePartitionEquiv transition hinj).symm (Sum.inr p) =
      M.transitionEdge transition p := by
  simp [edgePartitionEquiv]

@[simp]
private theorem edgePartitionEquiv_apply_unpaired {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition))
    (e : M.UnpairedTransitionEdge transition) :
    M.edgePartitionEquiv transition hinj e.1 = Sum.inl e := by
  apply (M.edgePartitionEquiv transition hinj).symm.injective
  simp

@[simp]
private theorem edgePartitionEquiv_apply_transitionEdge {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (p : T × Fin 2) :
    M.edgePartitionEquiv transition hinj (M.transitionEdge transition p) =
      Sum.inr p := by
  apply (M.edgePartitionEquiv transition hinj).symm.injective
  simp

private noncomputable def incidenceWeight (v : V) (e : E) : ZMod 2 := by
  classical
  exact if M.Inc v e then 1 else 0

private theorem degree_cast_eq_sum_incidence [Fintype E] (v : V) :
    (M.degree v : ZMod 2) = ∑ e : E, M.incidenceWeight v e := by
  classical
  rw [degree_eq_sum_incidence]
  simp [incidenceWeight]

private theorem transition_incidence_parity {T : Type*}
    (transition : T → M.EdgeTransition) (t : T) (v : V) :
    M.incidenceWeight v (transition t).left +
        M.incidenceWeight v (transition t).right =
      (M.compressTransitions transition).incidenceWeight v (Sum.inr t) := by
  classical
  have hbefore : (transition t).before ≠ (transition t).center := by
    intro h
    apply M.loopless (transition t).left (transition t).before
    simpa [h] using (transition t).left_ends
  have hafter : (transition t).center ≠ (transition t).after := by
    intro h
    apply M.loopless (transition t).right (transition t).center
    simpa [h] using (transition t).right_ends
  by_cases hvbefore : v = (transition t).before
  · subst v
    simp only [incidenceWeight, Inc, (transition t).left_ends, Sym2.mem_iff,
      hbefore, or_false, ↓reduceIte, (transition t).right_ends,
      (transition t).before_ne_after, or_self, add_zero, compressTransitions]
  · by_cases hvcenter : v = (transition t).center
    · subst v
      simp only [incidenceWeight, Inc, (transition t).left_ends, Sym2.mem_iff,
        Ne.symm hbefore, or_true, ↓reduceIte, (transition t).right_ends, hafter,
        or_false, compressTransitions, or_self]
      change ((2 : ℕ) : ZMod 2) = 0
      exact ZMod.natCast_eq_zero_iff_even.mpr even_two
    · by_cases hvafter : v = (transition t).after
      · subst v
        simp only [incidenceWeight, Inc, (transition t).left_ends, Sym2.mem_iff,
          hvbefore, hvcenter, or_self, ↓reduceIte, (transition t).right_ends,
          or_true, zero_add, compressTransitions]
      · simp [incidenceWeight, Inc, compressTransitions, (transition t).left_ends,
          (transition t).right_ends, Sym2.mem_iff, hvbefore, hvcenter, hvafter]

/-- Simultaneous compression of pairwise edge-disjoint transitions preserves degree parity. -/
private theorem compressTransitions_even_degree {T : Type*} [Finite E] [Finite T]
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition))
    (heven : ∀ v, Even (M.degree v)) (v : V) :
    Even ((M.compressTransitions transition).degree v) := by
  classical
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite T
  apply ZMod.natCast_eq_zero_iff_even.mp
  calc
    ((M.compressTransitions transition).degree v : ZMod 2) =
        ∑ e : M.CompressedTransitionEdge transition,
          (M.compressTransitions transition).incidenceWeight v e :=
      (M.compressTransitions transition).degree_cast_eq_sum_incidence v
    _ = (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
        ∑ t : T, (M.compressTransitions transition).incidenceWeight v (Sum.inr t) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
        ∑ t : T, (M.incidenceWeight v (transition t).left +
          M.incidenceWeight v (transition t).right) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact (M.transition_incidence_parity transition t v).symm
    _ = (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
        ∑ p : T × Fin 2, M.incidenceWeight v (M.transitionEdge transition p) := by
      rw [Fintype.sum_prod_type]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [Fin.sum_univ_two]
      simp [transitionEdge]
    _ = ∑ e : E, M.incidenceWeight v e := by
      calc
        (∑ e : M.UnpairedTransitionEdge transition, M.incidenceWeight v e.1) +
            ∑ p : T × Fin 2, M.incidenceWeight v (M.transitionEdge transition p) =
          ∑ z : M.UnpairedTransitionEdge transition ⊕ (T × Fin 2),
            M.incidenceWeight v ((M.edgePartitionEquiv transition hinj).symm z) := by
          rw [Fintype.sum_sum_type]
          simp
        _ = ∑ e : E, M.incidenceWeight v e :=
          (M.edgePartitionEquiv transition hinj).symm.sum_comp
            (M.incidenceWeight v)
    _ = (M.degree v : ZMod 2) := (M.degree_cast_eq_sum_incidence v).symm
    _ = 0 := ZMod.natCast_eq_zero_iff_even.mpr (heven v)

/-- The original edge identities represented by one compressed edge. -/
private def transitionExpansionEdges {T : Type*}
    (transition : T → M.EdgeTransition) :
    M.CompressedTransitionEdge transition → List E
  | Sum.inl e => [e.1]
  | Sum.inr t => [(transition t).left, (transition t).right]

/-- Two edge identities occur consecutively, in either order, in an edge list. -/
private def EdgesAdjacent (a b : E) (l : List E) : Prop :=
  ∃ before after, l = before ++ a :: b :: after ∨
    l = before ++ b :: a :: after

private theorem EdgesAdjacent.cons {a b : E} {l : List E}
    (h : EdgesAdjacent a b l) (e : E) : EdgesAdjacent a b (e :: l) := by
  rcases h with ⟨before, after, h | h⟩
  · exact ⟨e :: before, after, Or.inl (congrArg (e :: ·) h)⟩
  · exact ⟨e :: before, after, Or.inr (congrArg (e :: ·) h)⟩

/-- One expanded transition, together with its edge-list permutation. -/
private structure PrependedTransition [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {a b c : V}
    (e : M.CompressedTransitionEdge transition)
    (he : (M.compressTransitions transition).ends e = s(a, b))
    (q : M.IndexedWalk b c) where
  walk : M.IndexedWalk a c
  edges_perm : walk.edges.Perm (M.transitionExpansionEdges transition e ++ q.edges)
  edges_shape : match e with
    | Sum.inl f => walk.edges = f.1 :: q.edges
    | Sum.inr t => walk.edges = (transition t).left :: (transition t).right :: q.edges ∨
        walk.edges = (transition t).right :: (transition t).left :: q.edges

/-- Expand one compressed edge in front of an already expanded tail. -/
private def prependExpandedTransition [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {a b c : V}
    (e : M.CompressedTransitionEdge transition)
    (he : (M.compressTransitions transition).ends e = s(a, b))
    (q : M.IndexedWalk b c) : M.PrependedTransition transition e he q := by
  cases e with
  | inl e =>
      exact ⟨.cons e.1 he q, List.Perm.refl _, rfl⟩
  | inr t =>
      change s((transition t).before, (transition t).after) = s(a, b) at he
      by_cases ha : a = (transition t).before
      · subst a
        have hb : b = (transition t).after := by
          rcases Sym2.eq_iff.mp he with h | h
          · exact h.2.symm
          · exact False.elim ((transition t).before_ne_after h.2.symm)
        subst b
        exact ⟨.cons (transition t).left (transition t).left_ends
          (.cons (transition t).right (transition t).right_ends q),
          by simp [transitionExpansionEdges], Or.inl rfl⟩
      · have hab : a = (transition t).after ∧ b = (transition t).before := by
          rcases Sym2.eq_iff.mp he with h | h
          · exact False.elim (ha h.1.symm)
          · exact ⟨h.2.symm, h.1.symm⟩
        rcases hab with ⟨hafter, hbefore⟩
        subst a
        subst b
        refine ⟨.cons (transition t).right
          ((transition t).right_ends.trans Sym2.eq_swap)
          (.cons (transition t).left
            ((transition t).left_ends.trans Sym2.eq_swap) q), ?_, Or.inr rfl⟩
        exact List.Perm.swap (transition t).left (transition t).right q.edges

/-- An expanded compressed walk and its canonical edge-list permutation. -/
private structure ExpandedTransitions [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) where
  walk : M.IndexedWalk u v
  edges_perm : walk.edges.Perm
    (p.edges.flatMap (M.transitionExpansionEdges transition))
  edges_adjacent : ∀ t, Sum.inr t ∈ p.edges →
    EdgesAdjacent (transition t).left (transition t).right walk.edges

/-- Expand a compressed walk while retaining its edge-list permutation. -/
private def expandTransitionsWithEdges [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V} :
    (p : (M.compressTransitions transition).IndexedWalk u v) →
      M.ExpandedTransitions transition p
  | .nil w => ⟨.nil w, by simp, by simp⟩
  | .cons e he p =>
      let tail := expandTransitionsWithEdges transition p
      let step := M.prependExpandedTransition transition e he tail.walk
      ⟨step.walk, step.edges_perm.trans (tail.edges_perm.append_left _), by
        intro t ht
        rw [IndexedWalk.edges_cons] at ht
        rcases List.mem_cons.mp ht with het | ht
        · cases e with
          | inl e => simp at het
          | inr t' =>
              have htt : t' = t := Sum.inr.inj het.symm
              subst t'
              rcases step.edges_shape with h | h
              · rw [h]
                exact ⟨[], tail.walk.edges, Or.inl rfl⟩
              · rw [h]
                exact ⟨[], tail.walk.edges, Or.inr rfl⟩
        · have htail := tail.edges_adjacent t ht
          cases e with
          | inl e =>
              rw [step.edges_shape]
              exact htail.cons e.1
          | inr t' =>
              rcases step.edges_shape with h | h
              · rw [h]
                exact (htail.cons (transition t').right).cons
                  (transition t').left
              · rw [h]
                exact (htail.cons (transition t').left).cons
                  (transition t').right⟩

/-- Expand every temporary transition edge back to its two original indexed edges. -/
private def expandTransitions [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) : M.IndexedWalk u v :=
  (M.expandTransitionsWithEdges transition p).walk

/-- The expanded edge list is a permutation of the concatenated per-edge expansions. -/
private theorem expandTransitions_edges_perm [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) :
    (M.expandTransitions transition p).edges.Perm
      (p.edges.flatMap (M.transitionExpansionEdges transition)) :=
  (M.expandTransitionsWithEdges transition p).edges_perm

/-- Every forced pair occurs consecutively in the expanded edge list. -/
private theorem expandTransitions_edges_adjacent [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) (t : T)
    (ht : Sum.inr t ∈ p.edges) :
    EdgesAdjacent (transition t).left (transition t).right
      (M.expandTransitions transition p).edges :=
  (M.expandTransitionsWithEdges transition p).edges_adjacent t ht

/-- Map an original edge to the compressed edge that accounts for it. -/
private noncomputable def transitionOwner {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (e : E) :
    M.CompressedTransitionEdge transition :=
  match M.edgePartitionEquiv transition hinj e with
  | Sum.inl f => Sum.inl f
  | Sum.inr p => Sum.inr p.1

@[simp]
private theorem transitionOwner_unpaired {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition))
    (e : M.UnpairedTransitionEdge transition) :
    M.transitionOwner transition hinj e.1 = Sum.inl e := by
  classical
  have hpart : M.edgePartitionEquiv transition hinj e.1 = Sum.inl e := by
    apply (M.edgePartitionEquiv transition hinj).symm.injective
    simp
  simp [transitionOwner, hpart]

@[simp]
private theorem transitionOwner_transitionEdge {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (p : T × Fin 2) :
    M.transitionOwner transition hinj (M.transitionEdge transition p) =
      Sum.inr p.1 := by
  classical
  have hpart : M.edgePartitionEquiv transition hinj
      (M.transitionEdge transition p) = Sum.inr p := by
    apply (M.edgePartitionEquiv transition hinj).symm.injective
    simp
  simp [transitionOwner, hpart]

@[simp]
private theorem transitionOwner_left {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (t : T) :
    M.transitionOwner transition hinj (transition t).left = Sum.inr t := by
  simpa [transitionEdge] using
    M.transitionOwner_transitionEdge transition hinj (t, (0 : Fin 2))

@[simp]
private theorem transitionOwner_right {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (t : T) :
    M.transitionOwner transition hinj (transition t).right = Sum.inr t := by
  simpa [transitionEdge] using
    M.transitionOwner_transitionEdge transition hinj (t, (1 : Fin 2))

private theorem transitionOwner_eq_inl_iff {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (e : E)
    (f : M.UnpairedTransitionEdge transition) :
    M.transitionOwner transition hinj e = Sum.inl f ↔ e = f.1 := by
  classical
  constructor
  · intro h
    generalize hp : M.edgePartitionEquiv transition hinj e = z at h
    cases z with
    | inl g =>
        simp only [transitionOwner, hp, Sum.inl.injEq] at h
        subst g
        apply (M.edgePartitionEquiv transition hinj).injective
        simpa using hp
    | inr p => simp [transitionOwner, hp] at h
  · rintro rfl
    exact M.transitionOwner_unpaired transition hinj f

private theorem transitionOwner_eq_inr_iff {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (e : E) (t : T) :
    M.transitionOwner transition hinj e = Sum.inr t ↔
      e = (transition t).left ∨ e = (transition t).right := by
  classical
  constructor
  · intro h
    generalize hp : M.edgePartitionEquiv transition hinj e = z at h
    cases z with
    | inl f => simp [transitionOwner, hp] at h
    | inr p =>
        simp only [transitionOwner, hp, Sum.inr.injEq] at h
        have he : e = M.transitionEdge transition p := by
          apply (M.edgePartitionEquiv transition hinj).injective
          simpa using hp
        have hside : p.2 = 0 ∨ p.2 = 1 := by
          have hval : p.2.val = 0 ∨ p.2.val = 1 := by omega
          exact hval.imp Fin.ext Fin.ext
        rcases hside with hzero | hone
        · left
          rw [he, show p = (t, 0) by ext <;> simp [h, hzero], transitionEdge]
          simp
        · right
          rw [he, show p = (t, 1) by ext <;> simp [h, hone], transitionEdge]
          simp
  · rintro (rfl | rfl)
    · exact M.transitionOwner_left transition hinj t
    · exact M.transitionOwner_right transition hinj t

private theorem mem_transitionExpansionEdges_iff {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) (e : E)
    (f : M.CompressedTransitionEdge transition) :
    e ∈ M.transitionExpansionEdges transition f ↔
      M.transitionOwner transition hinj e = f := by
  cases f with
  | inl f =>
      simpa [transitionExpansionEdges] using
        (M.transitionOwner_eq_inl_iff transition hinj e f).symm
  | inr t =>
      simpa [transitionExpansionEdges] using
        (M.transitionOwner_eq_inr_iff transition hinj e t).symm

/-- An original edge occurs in the expansion exactly when its owner occurs in the compressed
walk. -/
private theorem mem_expandTransitions_edges_iff [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) {u v : V}
    (p : (M.compressTransitions transition).IndexedWalk u v) (e : E) :
    e ∈ (M.expandTransitions transition p).edges ↔
      M.transitionOwner transition hinj e ∈ p.edges := by
  rw [(M.expandTransitions_edges_perm transition p).mem_iff, List.mem_flatMap]
  constructor
  · rintro ⟨f, hf, he⟩
    rw [M.mem_transitionExpansionEdges_iff transition hinj e f] at he
    rwa [he]
  · intro he
    exact ⟨M.transitionOwner transition hinj e, he,
      (M.mem_transitionExpansionEdges_iff transition hinj e _).mpr rfl⟩

private theorem transitionExpansionEdges_nodup {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition))
    (f : M.CompressedTransitionEdge transition) :
    (M.transitionExpansionEdges transition f).Nodup := by
  cases f with
  | inl e => simp [transitionExpansionEdges]
  | inr t =>
      simp only [transitionExpansionEdges, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, not_false_eq_true]
      refine ⟨?_, by simp⟩
      intro h
      have hpairs : (t, (0 : Fin 2)) = (t, (1 : Fin 2)) := by
        apply hinj
        simpa [transitionEdge] using h
      exact Fin.zero_ne_one (congrArg Prod.snd hpairs)

private theorem flatMap_transitionExpansionEdges_nodup {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition))
    (l : List (M.CompressedTransitionEdge transition)) (hl : l.Nodup) :
    (l.flatMap (M.transitionExpansionEdges transition)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun f _ ↦ M.transitionExpansionEdges_nodup transition hinj f, ?_⟩
  apply hl.imp
  intro f g hfg
  rw [Function.onFun, List.disjoint_left]
  intro e hef heg
  have hf := (M.mem_transitionExpansionEdges_iff transition hinj e f).mp hef
  have hg := (M.mem_transitionExpansionEdges_iff transition hinj e g).mp heg
  exact hfg (hf.symm.trans hg)

/-- Expanding pairwise edge-disjoint transitions preserves an Euler circuit. -/
private theorem expandTransitions_isEulerian [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition)
    (hinj : Function.Injective (M.transitionEdge transition)) {u : V}
    (p : (M.compressTransitions transition).IndexedWalk u u)
    (hp : p.IsEulerian) : (M.expandTransitions transition p).IsEulerian := by
  constructor
  · apply (M.expandTransitions_edges_perm transition p).nodup_iff.mpr
    exact M.flatMap_transitionExpansionEdges_nodup transition hinj p.edges hp.1
  · intro e
    apply (M.mem_expandTransitions_edges_iff transition hinj p e).mpr
    exact hp.2 (M.transitionOwner transition hinj e)

end EdgeIndexedMultigraph

end SimpleGraph

/-! ## ParallelPairDeletion -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- Two distinct indexed edges having the same endpoints. -/
private structure ParallelPair where
  first : E
  second : E
  ne : first ≠ second
  ends_eq : M.ends first = M.ends second

/-- Select one edge identity from a parallel pair. -/
private def ParallelPair.edge {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) : Fin 2 → E :=
  fun i ↦ if i = 0 then p.first else p.second

private theorem ParallelPair.edge_injective {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) :
    Function.Injective p.edge := by
  intro i j hij
  have hi : i = 0 ∨ i = 1 := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hj : j = 0 ∨ j = 1 := by
    have hval : j.val = 0 ∨ j.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rfl
  · exact False.elim (p.ne (by simpa [ParallelPair.edge] using hij))
  · exact False.elim (p.ne (by simpa [ParallelPair.edge] using hij.symm))
  · rfl

private theorem ParallelPair.mem_range_edge_iff {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) (e : E) :
    e ∈ Set.range p.edge ↔ e = p.first ∨ e = p.second := by
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      exact hval.imp Fin.ext Fin.ext
    rcases hi with rfl | rfl
    · exact Or.inl (by simp [ParallelPair.edge])
    · exact Or.inr (by simp [ParallelPair.edge])
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [ParallelPair.edge]⟩
    · exact ⟨1, by simp [ParallelPair.edge]⟩

/-- The edge identities left after deleting a parallel pair. -/
private abbrev ErasedParallelPair (p : M.ParallelPair) :=
  {e : E // e ∉ Set.range p.edge}

private instance erasedParallelPairFinite [Finite E] (p : M.ParallelPair) :
    Finite (M.ErasedParallelPair p) :=
  inferInstance

/-- Delete both edge identities in a parallel pair. -/
private def eraseParallelPair (p : M.ParallelPair) :
    EdgeIndexedMultigraph V (M.ErasedParallelPair p) where
  ends e := M.ends e.1
  loopless e := M.loopless e.1

/-- Regard a transition whose edges survive deletion as a transition in the erased multigraph. -/
private def ParallelPair.liftTransition {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) (t : M.EdgeTransition)
    (hleft : t.left ∉ Set.range p.edge) (hright : t.right ∉ Set.range p.edge) :
    (M.eraseParallelPair p).EdgeTransition where
  left := ⟨t.left, hleft⟩
  right := ⟨t.right, hright⟩
  before := t.before
  center := t.center
  after := t.after
  left_ends := t.left_ends
  right_ends := t.right_ends
  before_ne_after := t.before_ne_after

/-- Lifting surviving transitions through a parallel-pair deletion preserves edge-disjointness. -/
private theorem ParallelPair.liftTransition_edge_injective
    {M : EdgeIndexedMultigraph V E} {T : Type*} (p : M.ParallelPair)
    (transition : T → M.EdgeTransition)
    (hleft : ∀ t, (transition t).left ∉ Set.range p.edge)
    (hright : ∀ t, (transition t).right ∉ Set.range p.edge)
    (hinj : Function.Injective (M.transitionEdge transition)) :
    Function.Injective ((M.eraseParallelPair p).transitionEdge
      (fun t ↦ p.liftTransition (transition t) (hleft t) (hright t))) := by
  intro a b hab
  apply hinj
  rcases a with ⟨a, side⟩
  rcases b with ⟨b, side'⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  all_goals
    have hval := congrArg Subtype.val hab
    simpa [transitionEdge, ParallelPair.liftTransition] using hval

private noncomputable def parallelPairPartition (p : M.ParallelPair) :
    E ≃ M.ErasedParallelPair p ⊕ Fin 2 := by
  classical
  exact
    (Equiv.sumCompl (fun e ↦ e ∈ Set.range p.edge)).symm |>.trans
      (Equiv.sumCongr (Equiv.ofInjective _ p.edge_injective).symm (Equiv.refl _)) |>.trans
      (Equiv.sumComm _ _)

@[simp]
private theorem parallelPairPartition_symm_apply_inl (p : M.ParallelPair)
    (e : M.ErasedParallelPair p) :
    (M.parallelPairPartition p).symm (Sum.inl e) = e.1 := by
  simp [parallelPairPartition]

@[simp]
private theorem parallelPairPartition_symm_apply_inr (p : M.ParallelPair)
    (i : Fin 2) :
    (M.parallelPairPartition p).symm (Sum.inr i) = p.edge i := by
  simp [parallelPairPartition]

/-- Deleting a parallel pair does not change the degree of a vertex outside that pair. -/
private theorem eraseParallelPair_degree_eq_of_not_inc [Finite E]
    (p : M.ParallelPair) (v : V) (hfirst : ¬M.Inc v p.first) :
    (M.eraseParallelPair p).degree v = M.degree v := by
  classical
  have hsecond : ¬M.Inc v p.second := by
    intro h
    apply hfirst
    rw [Inc] at h ⊢
    rwa [p.ends_eq]
  let f : {e : M.ErasedParallelPair p // (M.eraseParallelPair p).Inc v e} ≃
      {e : E // M.Inc v e} := {
    toFun := fun e ↦ ⟨e.1.1, e.2⟩
    invFun := fun e ↦ ⟨⟨e.1, by
      rw [p.mem_range_edge_iff]
      push Not
      exact ⟨fun h ↦ hfirst (h ▸ e.2), fun h ↦ hsecond (h ▸ e.2)⟩⟩, e.2⟩
    left_inv := by intro e; rfl
    right_inv := by intro e; rfl }
  rw [degree, degree]
  exact Set.ncard_congr' f

/-- Deleting two parallel edges preserves degree parity at every vertex. -/
private theorem eraseParallelPair_even_degree [Finite E] (p : M.ParallelPair)
    (heven : ∀ v, Even (M.degree v)) (v : V) :
    Even ((M.eraseParallelPair p).degree v) := by
  classical
  let _ := Fintype.ofFinite E
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hpair : M.incidenceWeight v p.first = M.incidenceWeight v p.second := by
    unfold incidenceWeight Inc
    rw [p.ends_eq]
  have hpair_zero : ∑ i : Fin 2, M.incidenceWeight v (p.edge i) = 0 := by
    rw [Fin.sum_univ_two]
    change M.incidenceWeight v p.first + M.incidenceWeight v p.second = 0
    rw [hpair]
    unfold incidenceWeight
    split
    · change ((2 : ℕ) : ZMod 2) = 0
      exact ZMod.natCast_eq_zero_iff_even.mpr even_two
    · simp
  have hpartition : (∑ e : E, M.incidenceWeight v e) =
      (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) +
        ∑ i : Fin 2, M.incidenceWeight v (p.edge i) := by
    calc
      (∑ e : E, M.incidenceWeight v e) =
          ∑ z : M.ErasedParallelPair p ⊕ Fin 2,
            M.incidenceWeight v ((M.parallelPairPartition p).symm z) :=
        ((M.parallelPairPartition p).symm.sum_comp (M.incidenceWeight v)).symm
      _ = (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) +
          ∑ i : Fin 2, M.incidenceWeight v (p.edge i) := by
        rw [Fintype.sum_sum_type]
        simp
  calc
    ((M.eraseParallelPair p).degree v : ZMod 2) =
        ∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1 := by
      rw [(M.eraseParallelPair p).degree_cast_eq_sum_incidence]
      rfl
    _ = (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) + 0 := by simp
    _ = (∑ e : M.ErasedParallelPair p, M.incidenceWeight v e.1) +
        ∑ i : Fin 2, M.incidenceWeight v (p.edge i) := by rw [hpair_zero]
    _ = ∑ e : E, M.incidenceWeight v e := hpartition.symm
    _ = (M.degree v : ZMod 2) := (M.degree_cast_eq_sum_incidence v).symm
    _ = 0 := ZMod.natCast_eq_zero_iff_even.mpr (heven v)

end EdgeIndexedMultigraph

end SimpleGraph

/-! ## CycleForcedTransitions -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- Edge identities in a trail system augmented by arbitrary parity-correcting cycle copies. -/
private abbrev AugmentedTrailEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :=
  c.TrailSystemEdge cover ⊕ c.CycleCopyEdge q

/-- A trail system augmented by arbitrary parity-correcting cycle copies. -/
private noncomputable def augmentedTrailMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    {d : Fin c.length → ℕ} (q : CyclicParityCompletion d) :
    EdgeIndexedMultigraph V (c.AugmentedTrailEdge cover q) :=
  (c.trailSystemMultigraph cover).disjointSum (c.cycleCopyMultigraph q)

/-- The original cycle edge at an index, viewed in the augmented trail multigraph. -/
private def augmentedOriginalEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (i : Fin c.length) : c.AugmentedTrailEdge cover q :=
  Sum.inl (Sum.inl (ULift.up i))

/-- The unique copied edge at an index whose copy count is one. -/
private def augmentedCopiedEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) : c.AugmentedTrailEdge cover q :=
  Sum.inr ⟨i, ⟨0, by omega⟩⟩

/-- A component-cover edge viewed in the augmented trail multigraph. -/
private def augmentedCoverEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (D : c.outsideGraph.ConnectedComponent) (e : (cover D).Edge) :
    c.AugmentedTrailEdge cover q :=
  Sum.inl (Sum.inr ⟨D, e⟩)

@[simp]
private theorem augmentedTrailMultigraph_ends_original (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (i : Fin c.length) :
    (c.augmentedTrailMultigraph cover q).ends
        (c.augmentedOriginalEdge cover q i) =
      s(c.getVert i, c.getVert (i + 1)) :=
  rfl

@[simp]
private theorem augmentedTrailMultigraph_ends_copy (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) :
    (c.augmentedTrailMultigraph cover q).ends
        (c.augmentedCopiedEdge cover q hi) =
      s(c.getVert i, c.getVert (i.val + 1)) :=
  rfl

@[simp]
private theorem augmentedTrailMultigraph_ends_cover (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (D : c.outsideGraph.ConnectedComponent) (e : (cover D).Edge) :
    (c.augmentedTrailMultigraph cover q).ends (c.augmentedCoverEdge cover q D e) =
      (cover D).multigraph.ends e :=
  rfl

/-- An original cycle edge and its parity-correcting copy form a parallel pair. -/
private noncomputable def cycleParallelPair (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i : Fin c.length} (hi : q.copies i = 1) :
    (c.augmentedTrailMultigraph cover q).ParallelPair where
  first := c.augmentedOriginalEdge cover q i
  second := c.augmentedCopiedEdge cover q hi
  ne := by simp [augmentedOriginalEdge, augmentedCopiedEdge]
  ends_eq := by
    rw [c.augmentedTrailMultigraph_ends_original,
      c.augmentedTrailMultigraph_ends_copy]

/-- Indices carrying a parity-correcting copy. -/
private abbrev ActiveCycleCopy {n : ℕ} [NeZero n] {d : Fin n → ℕ}
    (q : CyclicParityCompletion d) :=
  {i : Fin n // q.copies i = 1}

/-- The augmented edge identities remaining after one original/copy pair is deleted. -/
private abbrev CutAugmentedTrailEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) :=
  (c.augmentedTrailMultigraph cover q).ErasedParallelPair
    (c.cycleParallelPair cover q cut.2)

/-- Delete the original/copy pair at `cut` from the augmented trail multigraph. -/
private noncomputable def cutAugmentedTrailMultigraph (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) :
    EdgeIndexedMultigraph V (c.CutAugmentedTrailEdge cover q cut) :=
  (c.augmentedTrailMultigraph cover q).eraseParallelPair
    (c.cycleParallelPair cover q cut.2)

/-- Active copied-edge indices other than the deleted index. -/
private abbrev UncutActiveCycleCopy {n : ℕ} [NeZero n] {d : Fin n → ℕ}
    (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q) :=
  {i : ActiveCycleCopy q // i.1 ≠ cut.1}

/-- A retained original edge in the cut augmented multigraph. -/
private noncomputable def cutOriginalEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
    c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedOriginalEdge cover q j, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simpa [cycleParallelPair, augmentedOriginalEdge] using hj
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]

/-- A retained copied edge in the cut augmented multigraph. -/
private noncomputable def cutCopiedEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut) :
    c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedCopiedEdge cover q i.1.2, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]
  · intro h
    have hind := congrArg
      (fun e : c.AugmentedTrailEdge cover q ↦ match e with
        | Sum.inl _ => none
        | Sum.inr e => some e.1)
      h
    apply i.2
    exact Option.some.inj
      (by simpa [cycleParallelPair, augmentedCopiedEdge] using hind)

/-- A component-cover edge retained after deleting one cycle-edge pair. -/
private noncomputable def cutCoverEdge (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (D : c.outsideGraph.ConnectedComponent)
    (e : (cover D).Edge) : c.CutAugmentedTrailEdge cover q cut := by
  refine ⟨c.augmentedCoverEdge cover q D e, ?_⟩
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  simp [cycleParallelPair, augmentedCoverEdge, augmentedOriginalEdge,
    augmentedCopiedEdge]

@[simp]
private theorem cutAugmentedTrailMultigraph_ends_original (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
    (c.cutAugmentedTrailMultigraph cover q cut).ends
        (c.cutOriginalEdge cover q cut j hj) =
      s(c.getVert j, c.getVert (j + 1)) :=
  c.augmentedTrailMultigraph_ends_original cover q j

@[simp]
private theorem cutAugmentedTrailMultigraph_ends_copy (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut) :
    (c.cutAugmentedTrailMultigraph cover q cut).ends
        (c.cutCopiedEdge cover q cut i) =
      s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) :=
  c.augmentedTrailMultigraph_ends_copy cover q i.1.2

@[simp]
private theorem cutAugmentedTrailMultigraph_ends_cover (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (D : c.outsideGraph.ConnectedComponent)
    (e : (cover D).Edge) :
    (c.cutAugmentedTrailMultigraph cover q cut).ends
        (c.cutCoverEdge cover q cut D e) =
      (cover D).multigraph.ends e :=
  c.augmentedTrailMultigraph_ends_cover cover q D e

private theorem augmentedCopiedEdge_index_eq (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {i j : Fin c.length} (hi : q.copies i = 1) (hj : q.copies j = 1)
    (h : c.augmentedCopiedEdge cover q hi = c.augmentedCopiedEdge cover q hj) :
    i = j := by
  have hind := congrArg
    (fun e : c.AugmentedTrailEdge cover q ↦ match e with
      | Sum.inl _ => none
      | Sum.inr e => some e.1)
    h
  exact Option.some.inj (by simpa [augmentedCopiedEdge] using hind)

/-- The final cyclic edge index. -/
private def cycleLastIndex (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, by have := NeZero.pos n; omega⟩

/-- The active copied edge at the final cyclic index. -/
private def lastActiveCycleCopy {n : ℕ} [NeZero n] {d : Fin n → ℕ}
    (q : CyclicParityCompletion d) (hlast : q.copies (cycleLastIndex n) = 1) :
    ActiveCycleCopy q :=
  ⟨cycleLastIndex n, hlast⟩

private theorem fin_val_add_one_lt_of_ne_cycleLastIndex {n : ℕ} [NeZero n]
    (i : Fin n) (hi : i ≠ cycleLastIndex n) : i.val + 1 < n := by
  have hn : 0 < n := NeZero.pos n
  have hilast : i.val ≠ n - 1 := fun h ↦ hi (Fin.ext h)
  omega

private theorem ActiveCycleCopy.ne_zero {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (i : ActiveCycleCopy q) :
    i.1 ≠ 0 := by
  intro hi
  have hone := i.2
  rw [hi, q.copies_zero] at hone
  omega

private theorem ActiveCycleCopy.ne_of_copies_eq_zero {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (i : ActiveCycleCopy q)
    (j : Fin n) (hj : q.copies j = 0) : i.1 ≠ j := by
  intro hij
  subst j
  omega

private theorem ActiveCycleCopy.val_add_one_lt {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (i : ActiveCycleCopy q)
    (hlast : q.copies (cycleLastIndex n) = 0) : i.1.val + 1 < n := by
  have hn : 0 < n := NeZero.pos n
  have hilast : i.1 ≠ cycleLastIndex n :=
    i.ne_of_copies_eq_zero q _ hlast
  have hilastval : i.1.val ≠ n - 1 := by
    intro h
    apply hilast
    apply Fin.ext
    exact h
  have hi := i.1.isLt
  omega

/-- Forward forced transitions after deleting the copied closing edge and its original. -/
private noncomputable def forwardLastCutCycleTransition (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    UncutActiveCycleCopy q (lastActiveCycleCopy q hlast) →
      (c.cutAugmentedTrailMultigraph cover q
        (lastActiveCycleCopy q hlast)).EdgeTransition := by
  intro i
  let cut := lastActiveCycleCopy q hlast
  have hi0 := i.1.ne_zero q
  have hiend : i.1.1.val + 1 < c.length := by
    apply fin_val_add_one_lt_of_ne_cycleLastIndex
    simpa [cut, lastActiveCycleCopy] using i.2
  have hpartner : i.1.1 - 1 ≠ cut.1 := by
    intro heq
    have hval := congrArg Fin.val heq
    rw [Fin.val_sub_one_of_ne_zero hi0] at hval
    have hn : 0 < c.length := NeZero.pos c.length
    have hlt := i.1.1.isLt
    change i.1.1.val - 1 = c.length - 1 at hval
    omega
  have hleft :
      (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutOriginalEdge cover q cut (i.1.1 - 1) hpartner) =
        s(c.getVert (i.1.1.val - 1), c.getVert i.1.1.val) := by
    rw [c.cutAugmentedTrailMultigraph_ends_original]
    rw [Fin.val_sub_one_of_ne_zero hi0]
    have hpos : 0 < i.1.1.val :=
      Nat.pos_of_ne_zero (fun h ↦ hi0 (Fin.ext h))
    rw [Nat.sub_add_cancel hpos]
  have hright :
      (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutCopiedEdge cover q cut i) =
        s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) :=
    c.cutAugmentedTrailMultigraph_ends_copy cover q cut i
  exact {
    left := c.cutOriginalEdge cover q cut (i.1.1 - 1) hpartner
    right := c.cutCopiedEdge cover q cut i
    before := c.getVert (i.1.1.val - 1)
    center := c.getVert i.1.1.val
    after := c.getVert (i.1.1.val + 1)
    left_ends := hleft
    right_ends := hright
    before_ne_after :=
      hc.getVert_sub_one_ne_getVert_add_one (Nat.le_of_lt i.1.1.isLt) }

@[simp]
private theorem forwardLastCutCycleTransition_before (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
    (c.forwardLastCutCycleTransition hc cover q hlast i).before =
      c.getVert (i.1.1.val - 1) :=
  rfl

@[simp]
private theorem forwardLastCutCycleTransition_after (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
    (c.forwardLastCutCycleTransition hc cover q hlast i).after =
      c.getVert (i.1.1.val + 1) :=
  rfl

@[simp]
private theorem forwardLastCutCycleTransition_center (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
    (c.forwardLastCutCycleTransition hc cover q hlast i).center =
      c.getVert i.1.1 :=
  rfl

@[simp]
private theorem forwardLastCutCycleTransition_right (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
    (c.forwardLastCutCycleTransition hc cover q hlast i).right =
      c.cutCopiedEdge cover q (lastActiveCycleCopy q hlast) i :=
  rfl

/-- The forward closing-edge-cut transitions are pairwise edge-disjoint. -/
private theorem forwardLastCutCycleTransition_edge_injective (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    Function.Injective
      ((c.cutAugmentedTrailMultigraph cover q (lastActiveCycleCopy q hlast)).transitionEdge
        (c.forwardLastCutCycleTransition hc cover q hlast)) := by
  intro a b hab
  rcases a with ⟨i, side⟩
  rcases b with ⟨j, side'⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  · have hval := congrArg Subtype.val hab
    have hind : i.1.1 - 1 = j.1.1 - 1 := by
      simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
        cutOriginalEdge, augmentedOriginalEdge] using hval
    have hij : i = j := by
      apply Subtype.ext
      apply Subtype.ext
      exact sub_left_injective hind
    subst j
    rfl
  · have hval := congrArg Subtype.val hab
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge, augmentedCopiedEdge] at hval
  · have hval := congrArg Subtype.val hab
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge, augmentedCopiedEdge] at hval
  · have hval := congrArg Subtype.val hab
    have hind : i.1.1 = j.1.1 := by
      apply augmentedCopiedEdge_index_eq c cover q i.1.2 j.1.2
      simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
        cutCopiedEdge] using hval
    have hij : i = j := by
      apply Subtype.ext
      exact Subtype.ext hind
    subst j
    rfl

/-- The original edge paired with a copied edge on the two root-to-`k` arcs. -/
private def splitPartnerIndex {n : ℕ} [NeZero n] (k : Fin n) (i : Fin n) : Fin n :=
  if i.val < k.val then i - 1 else i + 1

private theorem splitPartnerIndex_val_on_active {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (i : ActiveCycleCopy q) :
    (splitPartnerIndex k i.1).val =
      if i.1.val < k.val then i.1.val - 1 else i.1.val + 1 := by
  by_cases h : i.1.val < k.val
  · rw [splitPartnerIndex, ite_eq_left h, ite_eq_left h,
      Fin.val_sub_one_of_ne_zero (i.ne_zero q)]
  · have hiend := i.val_add_one_lt q hlast
    have hn2 : 1 < n :=
      lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le i.1.val)) hiend
    have hone : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt hn2
    have hadd : i.1.val + (1 : Fin n).val < n := by
      rw [hone]
      exact hiend
    rw [splitPartnerIndex, ite_eq_right h, ite_eq_right h]
    exact (Fin.val_add_eq_of_add_lt hadd).trans (by rw [hone])

private theorem splitPartnerIndex_injective_on_active {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) :
    Function.Injective
      (fun i : ActiveCycleCopy q ↦ splitPartnerIndex k i.1) := by
  intro i j hij
  have hipos : 0 < i.1.val := by
    have hi0 := i.ne_zero q
    exact Nat.pos_of_ne_zero (fun h ↦ hi0 (Fin.ext h))
  have hjpos : 0 < j.1.val := by
    have hj0 := j.ne_zero q
    exact Nat.pos_of_ne_zero (fun h ↦ hj0 (Fin.ext h))
  apply Subtype.ext
  apply Fin.ext
  have hval := congrArg Fin.val hij
  change (splitPartnerIndex k i.1).val = (splitPartnerIndex k j.1).val at hval
  have hvali := splitPartnerIndex_val_on_active q k hlast i
  have hvalj := splitPartnerIndex_val_on_active q k hlast j
  have heq : (if i.1.val < k.val then i.1.val - 1 else i.1.val + 1) =
      if j.1.val < k.val then j.1.val - 1 else j.1.val + 1 :=
    hvali.symm.trans (hval.trans hvalj)
  by_cases hiklt : i.1.val < k.val <;> by_cases hjklt : j.1.val < k.val
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega

/-- The forced transition associated to every copied edge when neither terminal arc edge is
copied. -/
private noncomputable def splitCycleTransition (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    ActiveCycleCopy q → (c.augmentedTrailMultigraph cover q).EdgeTransition := by
  intro i
  let partner := splitPartnerIndex k i.1
  by_cases hforward : i.1.val < k.val
  · have hi0 := i.ne_zero q
    have hpartner : partner = i.1 - 1 := by simp [partner, splitPartnerIndex, hforward]
    have hleft :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q partner) =
          s(c.getVert (i.1.val - 1), c.getVert i.1.val) := by
      rw [hpartner, c.augmentedTrailMultigraph_ends_original]
      rw [Fin.val_sub_one_of_ne_zero hi0]
      have hpos : 0 < i.1.val := Nat.pos_of_ne_zero (by
        intro h
        apply hi0
        apply Fin.ext
        exact h)
      rw [Nat.sub_add_cancel hpos]
    have hright :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedCopiedEdge cover q i.2) =
          s(c.getVert i.1, c.getVert (i.1.val + 1)) :=
      c.augmentedTrailMultigraph_ends_copy cover q i.2
    exact {
      left := c.augmentedOriginalEdge cover q partner
      right := c.augmentedCopiedEdge cover q i.2
      before := c.getVert (i.1.val - 1)
      center := c.getVert i.1.val
      after := c.getVert (i.1.val + 1)
      left_ends := hleft
      right_ends := hright
      before_ne_after := by
        exact hc.getVert_sub_one_ne_getVert_add_one (Nat.le_of_lt i.1.isLt) }
  · have hiend := i.val_add_one_lt q hlast
    have hn2 : 1 < c.length :=
      lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le i.1.val)) hiend
    have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt hn2
    have hadd : i.1.val + (1 : Fin c.length).val < c.length := by
      rw [hone]
      exact hiend
    have hpartner : partner = i.1 + 1 := by simp [partner, splitPartnerIndex, hforward]
    have hleft :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q partner) =
          s(c.getVert (i.1.val + 2), c.getVert (i.1.val + 1)) := by
      rw [hpartner, c.augmentedTrailMultigraph_ends_original,
        Fin.val_add_eq_of_add_lt hadd, hone]
      exact Sym2.eq_swap
    have hright :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedCopiedEdge cover q i.2) =
          s(c.getVert (i.1.val + 1), c.getVert i.1.val) := by
      rw [c.augmentedTrailMultigraph_ends_copy, Sym2.eq_swap]
    exact {
      left := c.augmentedOriginalEdge cover q partner
      right := c.augmentedCopiedEdge cover q i.2
      before := c.getVert (i.1.val + 2)
      center := c.getVert (i.1.val + 1)
      after := c.getVert i.1.val
      left_ends := hleft
      right_ends := hright
      before_ne_after := by
        have hne := hc.getVert_sub_one_ne_getVert_add_one
          (i := i.1.val + 1) (by omega : i.1.val + 1 ≤ c.length)
        simpa using hne.symm }

@[simp]
private theorem splitCycleTransition_left (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) :
    (c.splitCycleTransition hc cover q k hlast i).left =
      c.augmentedOriginalEdge cover q (splitPartnerIndex k i.1) := by
  by_cases h : i.1.val < k.val <;> simp [splitCycleTransition, h]

@[simp]
private theorem splitCycleTransition_right (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) :
    (c.splitCycleTransition hc cover q k hlast i).right =
      c.augmentedCopiedEdge cover q i.2 := by
  by_cases h : i.1.val < k.val <;> simp [splitCycleTransition, h]

@[simp]
private theorem splitCycleTransition_before_of_lt (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
    (c.splitCycleTransition hc cover q k hlast i).before =
      c.getVert (i.1.val - 1) := by
  simp [splitCycleTransition, hi]

@[simp]
private theorem splitCycleTransition_after_of_lt (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
    (c.splitCycleTransition hc cover q k hlast i).after =
      c.getVert (i.1.val + 1) := by
  simp [splitCycleTransition, hi]

@[simp]
private theorem splitCycleTransition_center_of_lt (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
    (c.splitCycleTransition hc cover q k hlast i).center = c.getVert i.1 := by
  simp [splitCycleTransition, hi]

@[simp]
private theorem splitCycleTransition_before_of_not_lt (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
    (c.splitCycleTransition hc cover q k hlast i).before =
      c.getVert (i.1.val + 2) := by
  simp [splitCycleTransition, hi]

@[simp]
private theorem splitCycleTransition_after_of_not_lt (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
    (c.splitCycleTransition hc cover q k hlast i).after = c.getVert i.1.val := by
  simp [splitCycleTransition, hi]

@[simp]
private theorem splitCycleTransition_center_of_not_lt (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
    (c.splitCycleTransition hc cover q k hlast i).center =
      c.getVert (i.1.val + 1) := by
  simp [splitCycleTransition, hi]

private theorem splitPartnerIndex_ne_cut {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (hlast : q.copies (cycleLastIndex n) = 0)
    (i : UncutActiveCycleCopy q cut) :
    splitPartnerIndex cut.1 i.1.1 ≠ cut.1 := by
  intro h
  have hval := congrArg Fin.val h
  rw [splitPartnerIndex_val_on_active q cut.1 hlast i.1] at hval
  have hipos : 0 < i.1.1.val :=
    Nat.pos_of_ne_zero (fun hzero ↦ i.1.ne_zero q (Fin.ext hzero))
  by_cases hlt : i.1.1.val < cut.1.val
  · simp [hlt] at hval
    omega
  · simp [hlt] at hval
    have hneval : i.1.1.val ≠ cut.1.val := fun heq ↦ i.2 (Fin.ext heq)
    omega

private theorem splitCycleTransition_left_survives_cut (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).left ∉
      Set.range (c.cycleParallelPair cover q cut.2).edge := by
  rw [c.splitCycleTransition_left]
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simpa [cycleParallelPair, augmentedOriginalEdge] using
      splitPartnerIndex_ne_cut q cut hlast i
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]

private theorem splitCycleTransition_right_survives_cut (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.splitCycleTransition hc cover q cut.1 hlast i.1).right ∉
      Set.range (c.cycleParallelPair cover q cut.2).edge := by
  rw [c.splitCycleTransition_right]
  rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
  push Not
  constructor
  · simp [cycleParallelPair, augmentedOriginalEdge, augmentedCopiedEdge]
  · intro h
    exact i.2 (augmentedCopiedEdge_index_eq c cover q i.1.2 cut.2 h)

/-- Forced transitions after deleting the original/copy pair at the arc endpoint `cut`. -/
private noncomputable def cutSplitCycleTransition (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    UncutActiveCycleCopy q cut →
      (c.cutAugmentedTrailMultigraph cover q cut).EdgeTransition :=
  fun i ↦ (c.cycleParallelPair cover q cut.2).liftTransition
    (c.splitCycleTransition hc cover q cut.1 hlast i.1)
    (splitCycleTransition_left_survives_cut c hc cover q cut hlast i)
    (splitCycleTransition_right_survives_cut c hc cover q cut hlast i)

@[simp]
private theorem cutSplitCycleTransition_before (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.cutSplitCycleTransition hc cover q cut hlast i).before =
      (c.splitCycleTransition hc cover q cut.1 hlast i.1).before :=
  rfl

@[simp]
private theorem cutSplitCycleTransition_after (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.cutSplitCycleTransition hc cover q cut hlast i).after =
      (c.splitCycleTransition hc cover q cut.1 hlast i.1).after :=
  rfl

@[simp]
private theorem cutSplitCycleTransition_center (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.cutSplitCycleTransition hc cover q cut hlast i).center =
      (c.splitCycleTransition hc cover q cut.1 hlast i.1).center :=
  rfl

@[simp]
private theorem cutSplitCycleTransition_right (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) :
    (c.cutSplitCycleTransition hc cover q cut hlast i).right =
      c.cutCopiedEdge cover q cut i := by
  apply Subtype.ext
  exact c.splitCycleTransition_right hc cover q cut.1 hlast i.1

/-- The paired original/copy edge identities are all distinct. -/
private theorem splitCycleTransition_edge_injective (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    Function.Injective ((c.augmentedTrailMultigraph cover q).transitionEdge
      (c.splitCycleTransition hc cover q k hlast)) := by
  intro a b hab
  rcases a with ⟨i, side⟩
  rcases b with ⟨j, side'⟩
  have hpartner := splitPartnerIndex_injective_on_active q k hlast
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have hside' : side' = 0 ∨ side' = 1 := by
    have hval : side'.val = 0 ∨ side'.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl <;> rcases hside' with rfl | rfl
  · have hij : splitPartnerIndex k i.1 = splitPartnerIndex k j.1 := by
      simpa [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge] using hab
    have hij' : i = j := hpartner hij
    subst j
    rfl
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hab
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hab
  · have hij : i.1 = j.1 := by
      simp only [EdgeIndexedMultigraph.transitionEdge, Fin.isValue, one_ne_zero,
        ↓reduceIte, splitCycleTransition_right, augmentedCopiedEdge,
        Sum.inr.injEq, Sigma.mk.injEq] at hab
      exact hab.1
    apply Prod.ext
    · exact Subtype.ext hij
    · rfl

/-- The retained transition edges remain pairwise distinct after the endpoint cut. -/
private theorem cutSplitCycleTransition_edge_injective (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    Function.Injective ((c.cutAugmentedTrailMultigraph cover q cut).transitionEdge
      (c.cutSplitCycleTransition hc cover q cut hlast)) := by
  apply (c.cycleParallelPair cover q cut.2).liftTransition_edge_injective
  intro a b h
  change
    (c.augmentedTrailMultigraph cover q).transitionEdge
        (c.splitCycleTransition hc cover q cut.1 hlast) (a.1.1, a.2) =
      (c.augmentedTrailMultigraph cover q).transitionEdge
        (c.splitCycleTransition hc cover q cut.1 hlast) (b.1.1, b.2) at h
  have h' : (a.1.1, a.2) = (b.1.1, b.2) :=
    c.splitCycleTransition_edge_injective hc cover q cut.1 hlast h
  have hfst : a.1.1 = b.1.1 :=
    congrArg (fun z : ActiveCycleCopy q × Fin 2 ↦ z.1) h'
  have hsnd : a.2 = b.2 :=
    congrArg (fun z : ActiveCycleCopy q × Fin 2 ↦ z.2) h'
  exact Prod.ext (Subtype.ext hfst) hsnd

end Walk

end SimpleGraph

/-! ## ReplacedPath -/


namespace SimpleGraph

/-- A path remains connected to its terminal vertex when each selected internal step is
replaced by a skip over that vertex. -/
private theorem reachable_of_adj_or_skip {V : Type*} {G : SimpleGraph V}
    (v : ℕ → V) (m : ℕ) (selected : ℕ → Prop)
    (hterminal : ¬selected m)
    (hadj : ∀ i, i < m → ¬selected (i + 1) → G.Adj (v i) (v (i + 1)))
    (hskip : ∀ i, i + 2 ≤ m → selected (i + 1) → G.Adj (v i) (v (i + 2))) :
    ∀ i, i ≤ m → G.Reachable (v i) (v m) := by
  classical
  intro i hi
  have hbase : ∀ j, m ≤ j → j ≤ m → G.Reachable (v j) (v m) := by
    intro j hmj hjm
    have hj : j = m := by omega
    subst j
    exact ⟨Walk.nil⟩
  have hstep : ∀ k (hk : k < m),
      (∀ j, k + 1 ≤ j → j ≤ m → G.Reachable (v j) (v m)) →
        ∀ j, k ≤ j → j ≤ m → G.Reachable (v j) (v m) := by
    intro k hk ih j hkj hjm
    by_cases hjk : j = k
    · subst j
      by_cases hs : selected (k + 1)
      · have hk2 : k + 2 ≤ m := by
          by_contra h
          have hkm : k + 1 = m := by omega
          exact hterminal (hkm ▸ hs)
        exact (hskip k hk2 hs).reachable.trans (ih (k + 2) (by omega) hk2)
      · exact (hadj k hk hs).reachable.trans
          (ih (k + 1) (by omega) (by omega))
    · exact ih j (by omega) hjm
  exact Nat.decreasingInduction (motive := fun k hk ↦
    ∀ j, k ≤ j → j ≤ m → G.Reachable (v j) (v m)) hstep hbase hi i (le_refl i) hi

end SimpleGraph

/-! ## CycleTransitionConnectivity -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- The augmented trail multigraph after the two-arc transitions are compressed. -/
private noncomputable def splitCompressedMultigraph (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :=
  (c.augmentedTrailMultigraph cover q).compressTransitions
    (c.splitCycleTransition hc cover q k hlast)

/-- The closing-edge-cut multigraph after its forward transitions are compressed. -/
private noncomputable def forwardLastCutCompressedMultigraph (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :=
  (c.cutAugmentedTrailMultigraph cover q (lastActiveCycleCopy q hlast)).compressTransitions
    (c.forwardLastCutCycleTransition hc cover q hlast)

/-- The distinguished-edge-cut multigraph after its two-arc transitions are compressed. -/
private noncomputable def cutSplitCompressedMultigraph (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :=
  (c.cutAugmentedTrailMultigraph cover q cut).compressTransitions
    (c.cutSplitCycleTransition hc cover q cut hlast)

private theorem split_original_not_paired (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (j : Fin c.length)
    (hj : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j) :
    c.augmentedOriginalEdge cover q j ∉ Set.range
      ((c.augmentedTrailMultigraph cover q).transitionEdge
        (c.splitCycleTransition hc cover q k hlast)) := by
  rintro ⟨⟨i, side⟩, he⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl
  · apply hj i
    simpa [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge] using he
  · simp [EdgeIndexedMultigraph.transitionEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at he

private theorem split_compressed_adj_original (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (j : Fin c.length)
    (hj : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
      (c.getVert j) (c.getVert (j + 1)) := by
  apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
  exact ⟨Sum.inl ⟨c.augmentedOriginalEdge cover q j,
    c.split_original_not_paired hc cover q k hlast j hj⟩,
    c.augmentedTrailMultigraph_ends_original cover q j⟩

private theorem split_compressed_adj_forward_skip (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : i.1.val < k.val) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
      (c.getVert (i.1.val - 1)) (c.getVert (i.1.val + 1)) := by
  apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.splitCycleTransition hc cover q k hlast i).before,
    (c.splitCycleTransition hc cover q k hlast i).after) = _
  rw [c.splitCycleTransition_before_of_lt hc cover q k hlast i hi,
    c.splitCycleTransition_after_of_lt hc cover q k hlast i hi]

private theorem split_compressed_adj_reverse_skip (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : ActiveCycleCopy q) (hi : ¬i.1.val < k.val) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
      (c.getVert (i.1.val + 2)) (c.getVert i.1.val) := by
  apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.splitCycleTransition hc cover q k hlast i).before,
    (c.splitCycleTransition hc cover q k hlast i).after) = _
  rw [c.splitCycleTransition_before_of_not_lt hc cover q k hlast i hi,
    c.splitCycleTransition_after_of_not_lt hc cover q k hlast i hi]

private theorem split_partner_ne_forward_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k j : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (hjk : j.val < k.val)
    (hzero : ∀ h : j.val + 1 < k.val,
      q.copies ⟨j.val + 1, lt_trans h k.isLt⟩ = 0)
    (i : ActiveCycleCopy q) : splitPartnerIndex k i.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q k hlast i] at hval
  have hipos : 0 < i.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.ne_zero q (Fin.ext h))
  by_cases hik : i.1.val < k.val
  · simp [hik] at hval
    have hjnext : j.val + 1 < k.val := by omega
    have hinext : i.1 = ⟨j.val + 1, lt_trans hjnext k.isLt⟩ := by
      apply Fin.ext
      change i.1.val = j.val + 1
      omega
    have hone := i.2
    rw [hinext, hzero hjnext] at hone
    omega
  · simp [hik] at hval
    omega

private theorem split_partner_ne_reverse_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k j : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (hkj : k.val ≤ j.val)
    (hzero : k.val < j.val →
      q.copies ⟨j.val - 1, by omega⟩ = 0)
    (i : ActiveCycleCopy q) : splitPartnerIndex k i.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q k hlast i] at hval
  have hipos : 0 < i.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.ne_zero q (Fin.ext h))
  by_cases hik : i.1.val < k.val
  · simp [hik] at hval
    omega
  · simp [hik] at hval
    have hiend := i.val_add_one_lt q hlast
    by_cases hkj' : k.val = j.val
    · omega
    · have hkjlt : k.val < j.val := by omega
      have hiprev : i.1 = ⟨j.val - 1, by omega⟩ := by
        apply Fin.ext
        change i.1.val = j.val - 1
        omega
      have hone := i.2
      rw [hiprev, hzero hkjlt] at hone
      omega

private theorem split_forward_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hr : r ≤ k.val) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable
      (c.getVert r) x := by
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < k.val ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected k.val := by
    rintro ⟨hklen, hkk, hcopy⟩
    omega
  have hadj : ∀ i, i < k.val → ¬selected (i + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i hik hnsel
    let j : Fin c.length := ⟨i, lt_trans hik k.isLt⟩
    apply c.split_compressed_adj_original hc cover q k hlast j
    apply split_partner_ne_forward_original q k j hlast
    · exact hik
    · intro hinext
      have hcopy : q.copies
          ⟨j.val + 1, lt_trans hinext k.isLt⟩ = 0 := by
        by_contra hzero
        have hone : q.copies ⟨j.val + 1, lt_trans hinext k.isLt⟩ = 1 := by
          have hlt := q.copies_lt_two ⟨j.val + 1, lt_trans hinext k.isLt⟩
          omega
        apply hnsel
        exact ⟨lt_trans hinext k.isLt, hinext, hone⟩
      exact hcopy
  have hskip : ∀ i, i + 2 ≤ k.val → selected (i + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1k, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have h := c.split_compressed_adj_forward_skip hc cover q k hlast a hi1k
    simpa [a] using h
  have hpath := reachable_of_adj_or_skip
    (G := (c.splitCompressedMultigraph hc cover q k hlast).underlying)
    (fun i ↦ c.getVert i) k.val selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le k.val)
  exact (hpath r hr).trans (by simpa using hroot.symm)

private theorem split_reverse_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hkr : k.val ≤ r) (hrn : r < c.length) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - k.val
  let selected : ℕ → Prop := fun t ↦
    ∃ i : ActiveCycleCopy q, ¬i.1.val < k.val ∧ i.1.val + t + 1 = c.length
  have hterminal : ¬selected m := by
    rintro ⟨i, hik, hi⟩
    dsimp [m] at hi
    omega
  have hadj : ∀ a, a < m → ¬selected (a + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 1))) := by
    intro a ham hnsel
    let j : Fin c.length := ⟨c.length - a - 1, by
      have hn := NeZero.pos c.length
      dsimp [m] at ham
      omega⟩
    have hkj : k.val ≤ j.val := by
      dsimp [j, m] at ham ⊢
      omega
    have hnotpaired : ∀ i : ActiveCycleCopy q, splitPartnerIndex k i.1 ≠ j := by
      apply split_partner_ne_reverse_original q k j hlast hkj
      intro hkjlt
      by_contra hzero
      have hone : q.copies ⟨j.val - 1, by omega⟩ = 1 := by
        have hlt := q.copies_lt_two ⟨j.val - 1, by omega⟩
        omega
      let i : ActiveCycleCopy q := ⟨⟨j.val - 1, by omega⟩, hone⟩
      apply hnsel
      refine ⟨i, ?_, ?_⟩
      · dsimp [i]
        omega
      · change (j.val - 1) + (a + 1) + 1 = c.length
        have hjval : j.val = c.length - a - 1 := rfl
        omega
    have horig := c.split_compressed_adj_original hc cover q k hlast j hnotpaired
    have hsucc : c.getVert (j + 1) = c.getVert (c.length - a) := by
      congr 1
      dsimp [j, m] at ham ⊢
      omega
    rw [hsucc] at horig
    exact horig.symm
  have hskip : ∀ a, a + 2 ≤ m → selected (a + 1) →
      (c.splitCompressedMultigraph hc cover q k hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 2))) := by
    rintro a ha2 ⟨i, hik, hi⟩
    have h := c.split_compressed_adj_reverse_skip hc cover q k hlast i hik
    dsimp [m] at ha2
    convert h using 1 <;> congr 1 <;> omega
  have hpath := reachable_of_adj_or_skip
    (G := (c.splitCompressedMultigraph hc cover q k hlast).underlying)
    (fun t ↦ c.getVert (c.length - t)) m selected hterminal hadj hskip
  have ht : c.length - r ≤ m := by
    dsimp [m]
    omega
  have hroot := hpath 0 (Nat.zero_le m)
  have hrpath := hpath (c.length - r) ht
  simpa [m, Nat.sub_sub_self (Nat.le_of_lt hrn)] using hrpath.trans hroot.symm

private theorem split_cycle_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (v : V) (hv : v ∈ c.support) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Reachable v x := by
  let i := hc.finLengthEquivSupport.symm ⟨v, hv⟩
  have hvi : c.getVert i = v := by
    apply (hc.finLengthEquivSupport_apply i).symm.trans
    simpa only [i] using
      congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩)
  rw [← hvi]
  by_cases hik : i.val ≤ k.val
  · exact c.split_forward_reachable_root hc cover q k hlast i.val hik
  · exact c.split_reverse_reachable_root hc cover q k hlast i.val
      (by omega) i.isLt

private noncomputable def splitCompressedCoverHom (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.splitCompressedMultigraph hc cover q k hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    apply (c.splitCompressedMultigraph hc cover q k hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨c.augmentedCoverEdge cover q D e, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hside : side = 0 ∨ side = 1 := by
        have hval : side.val = 0 ∨ side.val = 1 := by omega
        exact hval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · simp [EdgeIndexedMultigraph.transitionEdge, augmentedCoverEdge,
          augmentedOriginalEdge] at hi
      · simp [EdgeIndexedMultigraph.transitionEdge, augmentedCoverEdge,
          augmentedCopiedEdge] at hi
    · exact (c.augmentedTrailMultigraph_ends_cover cover q D e).trans he

/-- Compressing the two root-to-`k` transition families preserves connectedness. -/
private theorem splitCompressedMultigraph_connected (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    (c.splitCompressedMultigraph hc cover q k hlast).underlying.Connected := by
  exact c.connected_of_cycle_reachable_and_component_covers cover
    (c.splitCompressedMultigraph hc cover q k hlast).underlying
    (c.split_cycle_reachable_root hc cover q k hlast)
    (c.splitCompressedCoverHom hc cover q k hlast) (by intros; rfl)

private theorem forwardLast_original_not_paired (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) (j : Fin c.length)
    (hjcut : j ≠ cycleLastIndex c.length)
    (hj : ∀ i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast),
      i.1.1 - 1 ≠ j) :
    c.cutOriginalEdge cover q (lastActiveCycleCopy q hlast) j (by
      simpa [lastActiveCycleCopy] using hjcut) ∉ Set.range
      ((c.cutAugmentedTrailMultigraph cover q
        (lastActiveCycleCopy q hlast)).transitionEdge
        (c.forwardLastCutCycleTransition hc cover q hlast)) := by
  rintro ⟨⟨i, side⟩, he⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl
  · apply hj i
    have hval := congrArg Subtype.val he
    simpa [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, augmentedOriginalEdge] using hval
  · have hval := congrArg Subtype.val he
    simp [EdgeIndexedMultigraph.transitionEdge, forwardLastCutCycleTransition,
      cutOriginalEdge, cutCopiedEdge, augmentedOriginalEdge,
      augmentedCopiedEdge] at hval

private theorem forwardLast_compressed_adj_original (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) (j : Fin c.length)
    (hjcut : j ≠ cycleLastIndex c.length)
    (hj : ∀ i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast),
      i.1.1 - 1 ≠ j) :
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
      (c.getVert j) (c.getVert (j + 1)) := by
  let cut := lastActiveCycleCopy q hlast
  have hjcut' : j ≠ cut.1 := by simpa [cut, lastActiveCycleCopy] using hjcut
  apply (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying_adj.mpr
  exact ⟨Sum.inl ⟨c.cutOriginalEdge cover q cut j hjcut',
    c.forwardLast_original_not_paired hc cover q hlast j hjcut hj⟩,
    c.cutAugmentedTrailMultigraph_ends_original cover q cut j hjcut'⟩

private theorem forwardLast_compressed_adj_skip (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (i : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast)) :
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
      (c.getVert (i.1.1.val - 1)) (c.getVert (i.1.1.val + 1)) := by
  apply (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.forwardLastCutCycleTransition hc cover q hlast i).before,
    (c.forwardLastCutCycleTransition hc cover q hlast i).after) = _
  rw [c.forwardLastCutCycleTransition_before hc cover q hlast i,
    c.forwardLastCutCycleTransition_after hc cover q hlast i]

private theorem forwardLast_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (r : ℕ) (hr : r ≤ c.length - 1) :
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - 1
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < m ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected m := by
    rintro ⟨hmlen, hmm, hcopy⟩
    omega
  have hadj : ∀ i, i < m → ¬selected (i + 1) →
      (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i him hnsel
    let j : Fin c.length := ⟨i, by dsimp [m] at him; omega⟩
    have hjcut : j ≠ cycleLastIndex c.length := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [j, cycleLastIndex, m] at hval him
      omega
    apply c.forwardLast_compressed_adj_original hc cover q hlast j hjcut
    intro a heq
    have hval := congrArg Fin.val heq
    have hapos : 0 < a.1.1.val :=
      Nat.pos_of_ne_zero (fun h ↦ a.1.ne_zero q (Fin.ext h))
    rw [Fin.val_sub_one_of_ne_zero (a.1.ne_zero q)] at hval
    dsimp [j] at hval
    have hauncut : a.1.1 ≠ cycleLastIndex c.length := by
      simpa [lastActiveCycleCopy] using a.2
    have halt : a.1.1.val < m := by
      have hne : a.1.1.val ≠ c.length - 1 := fun h ↦ hauncut (Fin.ext h)
      dsimp [m]
      omega
    have haveq : a.1.1.val = i + 1 := by omega
    apply hnsel
    have hi1len : i + 1 < c.length := by rw [← haveq]; exact a.1.1.isLt
    have hi1m : i + 1 < m := by rwa [← haveq]
    refine ⟨hi1len, hi1m, ?_⟩
    rw [show (⟨i + 1, hi1len⟩ : Fin c.length) = a.1.1 by exact Fin.ext haveq.symm]
    exact a.1.2
  have hskip : ∀ i, i + 2 ≤ m → selected (i + 1) →
      (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1m, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have hane : a.1 ≠ (lastActiveCycleCopy q hlast).1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [a, lastActiveCycleCopy, cycleLastIndex, m] at hval hi1m
      omega
    let a' : UncutActiveCycleCopy q (lastActiveCycleCopy q hlast) := ⟨a, hane⟩
    have h := c.forwardLast_compressed_adj_skip hc cover q hlast a'
    change (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Adj
      (c.getVert ((i + 1) - 1)) (c.getVert ((i + 1) + 1)) at h
    convert h using 1
    all_goals congr 1
  have hpath := reachable_of_adj_or_skip
    (G := (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying)
    (fun i ↦ c.getVert i) m selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le m)
  exact (hpath r hr).trans (by simpa using hroot.symm)

private noncomputable def forwardLastCompressedCoverHom (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    let cut := lastActiveCycleCopy q hlast
    let edge := c.cutCoverEdge cover q cut D e
    apply (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨edge, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hval := congrArg Subtype.val hi
      have hside : side = 0 ∨ side = 1 := by
        have hsval : side.val = 0 ∨ side.val = 1 := by omega
        exact hsval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedOriginalEdge cover q (i.1.1 - 1) := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            forwardLastCutCycleTransition, cutCoverEdge, cutOriginalEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedOriginalEdge] at hcycle
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedCopiedEdge cover q i.1.2 := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            forwardLastCutCycleTransition, cutCoverEdge, cutCopiedEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedCopiedEdge] at hcycle
    · exact (c.cutAugmentedTrailMultigraph_ends_cover cover q cut D e).trans he

/-- Deleting the copied closing edge and compressing all forward transitions preserves
connectedness. -/
private theorem forwardLastCutCompressedMultigraph_connected (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Connected := by
  have hcycle : ∀ v, v ∈ c.support →
      (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying.Reachable v x := by
    intro v hv
    let i := hc.finLengthEquivSupport.symm ⟨v, hv⟩
    have hvi : c.getVert i = v := by
      apply (hc.finLengthEquivSupport_apply i).symm.trans
      simpa only [i] using
        congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩)
    rw [← hvi]
    apply c.forwardLast_reachable_root hc cover q hlast i.val
    omega
  exact c.connected_of_cycle_reachable_and_component_covers cover
    (c.forwardLastCutCompressedMultigraph hc cover q hlast).underlying hcycle
    (c.forwardLastCompressedCoverHom hc cover q hlast) (by intros; rfl)

private theorem cutSplit_original_not_paired (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (j : Fin c.length) (hjcut : j ≠ cut.1)
    (hj : ∀ i : UncutActiveCycleCopy q cut,
      splitPartnerIndex cut.1 i.1.1 ≠ j) :
    c.cutOriginalEdge cover q cut j hjcut ∉ Set.range
      ((c.cutAugmentedTrailMultigraph cover q cut).transitionEdge
        (c.cutSplitCycleTransition hc cover q cut hlast)) := by
  rintro ⟨⟨i, side⟩, he⟩
  have hside : side = 0 ∨ side = 1 := by
    have hval : side.val = 0 ∨ side.val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases hside with rfl | rfl
  · apply hj i
    have hval := congrArg Subtype.val he
    simpa [EdgeIndexedMultigraph.transitionEdge, cutSplitCycleTransition,
      EdgeIndexedMultigraph.ParallelPair.liftTransition, cutOriginalEdge,
      augmentedOriginalEdge] using hval
  · have hval := congrArg Subtype.val he
    simp [EdgeIndexedMultigraph.transitionEdge, cutSplitCycleTransition,
      EdgeIndexedMultigraph.ParallelPair.liftTransition, cutOriginalEdge,
      augmentedOriginalEdge, augmentedCopiedEdge] at hval

private theorem cutSplit_compressed_adj_original (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (j : Fin c.length) (hjcut : j ≠ cut.1)
    (hj : ∀ i : UncutActiveCycleCopy q cut,
      splitPartnerIndex cut.1 i.1.1 ≠ j) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
      (c.getVert j) (c.getVert (j + 1)) := by
  apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
  exact ⟨Sum.inl ⟨c.cutOriginalEdge cover q cut j hjcut,
    c.cutSplit_original_not_paired hc cover q cut hlast j hjcut hj⟩,
    c.cutAugmentedTrailMultigraph_ends_original cover q cut j hjcut⟩

private theorem cutSplit_compressed_adj_forward_skip (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) (hi : i.1.1.val < cut.1.val) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
      (c.getVert (i.1.1.val - 1)) (c.getVert (i.1.1.val + 1)) := by
  apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.cutSplitCycleTransition hc cover q cut hlast i).before,
    (c.cutSplitCycleTransition hc cover q cut hlast i).after) = _
  rw [c.cutSplitCycleTransition_before, c.cutSplitCycleTransition_after,
    c.splitCycleTransition_before_of_lt hc cover q cut.1 hlast i.1 hi,
    c.splitCycleTransition_after_of_lt hc cover q cut.1 hlast i.1 hi]

private theorem cutSplit_compressed_adj_reverse_skip (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy q cut) (hi : ¬i.1.1.val < cut.1.val) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
      (c.getVert (i.1.1.val + 2)) (c.getVert i.1.1.val) := by
  apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
  refine ⟨Sum.inr i, ?_⟩
  change s((c.cutSplitCycleTransition hc cover q cut hlast i).before,
    (c.cutSplitCycleTransition hc cover q cut hlast i).after) = _
  rw [c.cutSplitCycleTransition_before, c.cutSplitCycleTransition_after,
    c.splitCycleTransition_before_of_not_lt hc cover q cut.1 hlast i.1 hi,
    c.splitCycleTransition_after_of_not_lt hc cover q cut.1 hlast i.1 hi]

private theorem cutSplit_forward_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hr : r ≤ cut.1.val) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable
      (c.getVert r) x := by
  let selected : ℕ → Prop := fun t ↦
    ∃ ht : t < c.length, t < cut.1.val ∧ q.copies ⟨t, ht⟩ = 1
  have hterminal : ¬selected cut.1.val := by
    rintro ⟨hlen, hlt, hcopy⟩
    omega
  have hadj : ∀ i, i < cut.1.val → ¬selected (i + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 1)) := by
    intro i hicut hnsel
    let j : Fin c.length := ⟨i, lt_trans hicut cut.1.isLt⟩
    have hjcut : j ≠ cut.1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [j] at hval
      omega
    apply c.cutSplit_compressed_adj_original hc cover q cut hlast j hjcut
    intro a
    apply split_partner_ne_forward_original q cut.1 j hlast hicut
    intro hinext
    by_contra hzero
    have hone : q.copies ⟨j.val + 1, lt_trans hinext cut.1.isLt⟩ = 1 := by
      have hlt := q.copies_lt_two ⟨j.val + 1, lt_trans hinext cut.1.isLt⟩
      omega
    apply hnsel
    exact ⟨lt_trans hinext cut.1.isLt, hinext, hone⟩
  have hskip : ∀ i, i + 2 ≤ cut.1.val → selected (i + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert i) (c.getVert (i + 2)) := by
    rintro i hi2 ⟨hi1len, hi1cut, hcopy⟩
    let a : ActiveCycleCopy q := ⟨⟨i + 1, hi1len⟩, hcopy⟩
    have hane : a.1 ≠ cut.1 := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [a] at hval
      omega
    let a' : UncutActiveCycleCopy q cut := ⟨a, hane⟩
    have h := c.cutSplit_compressed_adj_forward_skip hc cover q cut hlast a' hi1cut
    change (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
      (c.getVert ((i + 1) - 1)) (c.getVert ((i + 1) + 1)) at h
    convert h using 1
    all_goals congr 1
  have hpath := reachable_of_adj_or_skip
    (G := (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying)
    (fun i ↦ c.getVert i) cut.1.val selected hterminal hadj hskip
  have hroot := hpath 0 (Nat.zero_le cut.1.val)
  exact (hpath r hr).trans (by simpa using hroot.symm)

private theorem cut_split_partner_ne_reverse_original {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (j : Fin n) (hlast : q.copies (cycleLastIndex n) = 0)
    (hcutj : cut.1.val < j.val)
    (hzero : cut.1.val + 1 < j.val → q.copies ⟨j.val - 1, by omega⟩ = 0)
    (i : UncutActiveCycleCopy q cut) :
    splitPartnerIndex cut.1 i.1.1 ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [splitPartnerIndex_val_on_active q cut.1 hlast i.1] at hval
  have hipos : 0 < i.1.1.val :=
    Nat.pos_of_ne_zero (fun h ↦ i.1.ne_zero q (Fin.ext h))
  by_cases hik : i.1.1.val < cut.1.val
  · simp [hik] at hval
    omega
  · simp [hik] at hval
    by_cases hjnext : j.val = cut.1.val + 1
    · apply i.2
      apply Fin.ext
      omega
    · have hcutj' : cut.1.val + 1 < j.val := by omega
      have hiprev : i.1.1 = ⟨j.val - 1, by omega⟩ := by
        apply Fin.ext
        change i.1.1.val = j.val - 1
        omega
      have hone := i.1.2
      rw [hiprev, hzero hcutj'] at hone
      omega

private theorem cutSplit_reverse_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (r : ℕ) (hcutr : cut.1.val + 1 ≤ r) (hrn : r < c.length) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable
      (c.getVert r) x := by
  let m := c.length - (cut.1.val + 1)
  let selected : ℕ → Prop := fun t ↦
    ∃ i : UncutActiveCycleCopy q cut,
      ¬i.1.1.val < cut.1.val ∧ i.1.1.val + t + 1 = c.length
  have hterminal : ¬selected m := by
    rintro ⟨i, hik, hi⟩
    have hval : i.1.1.val = cut.1.val := by
      dsimp [m] at hi
      omega
    exact i.2 (Fin.ext hval)
  have hadj : ∀ a, a < m → ¬selected (a + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 1))) := by
    intro a ham hnsel
    let j : Fin c.length := ⟨c.length - a - 1, by
      have hn := NeZero.pos c.length
      dsimp [m] at ham
      omega⟩
    have hcutj : cut.1.val < j.val := by
      dsimp [j, m] at ham ⊢
      omega
    have hjcut : j ≠ cut.1 := fun h ↦ by
      have hval := congrArg Fin.val h
      omega
    have hnotpaired : ∀ i : UncutActiveCycleCopy q cut,
        splitPartnerIndex cut.1 i.1.1 ≠ j := by
      intro i
      apply cut_split_partner_ne_reverse_original q cut j hlast hcutj
      intro hcutj'
      by_contra hzero
      have hone : q.copies ⟨j.val - 1, by omega⟩ = 1 := by
        have hlt := q.copies_lt_two ⟨j.val - 1, by omega⟩
        omega
      let i' : ActiveCycleCopy q := ⟨⟨j.val - 1, by omega⟩, hone⟩
      have hine : i'.1 ≠ cut.1 := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [i'] at hval
        omega
      apply hnsel
      refine ⟨⟨i', hine⟩, ?_, ?_⟩
      · dsimp [i']
        omega
      · change (j.val - 1) + (a + 1) + 1 = c.length
        have hjval : j.val = c.length - a - 1 := rfl
        omega
    have horig :=
      c.cutSplit_compressed_adj_original hc cover q cut hlast j hjcut hnotpaired
    have hsucc : c.getVert (j + 1) = c.getVert (c.length - a) := by
      congr 1
      dsimp [j, m] at ham ⊢
      omega
    rw [hsucc] at horig
    exact horig.symm
  have hskip : ∀ a, a + 2 ≤ m → selected (a + 1) →
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Adj
        (c.getVert (c.length - a)) (c.getVert (c.length - (a + 2))) := by
    rintro a ha2 ⟨i, hik, hi⟩
    have h := c.cutSplit_compressed_adj_reverse_skip hc cover q cut hlast i hik
    dsimp [m] at ha2
    convert h using 1 <;> congr 1 <;> omega
  have hpath := reachable_of_adj_or_skip
    (G := (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying)
    (fun t ↦ c.getVert (c.length - t)) m selected hterminal hadj hskip
  have ht : c.length - r ≤ m := by
    dsimp [m]
    omega
  have hroot := hpath 0 (Nat.zero_le m)
  have hrpath := hpath (c.length - r) ht
  simpa [m, Nat.sub_sub_self (Nat.le_of_lt hrn)] using hrpath.trans hroot.symm

private theorem cutSplit_cycle_reachable_root (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (v : V) (hv : v ∈ c.support) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Reachable v x := by
  let i := hc.finLengthEquivSupport.symm ⟨v, hv⟩
  have hvi : c.getVert i = v := by
    apply (hc.finLengthEquivSupport_apply i).symm.trans
    simpa only [i] using
      congrArg Subtype.val (hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩)
  rw [← hvi]
  by_cases hicut : i.val ≤ cut.1.val
  · exact c.cutSplit_forward_reachable_root hc cover q cut hlast i.val hicut
  · exact c.cutSplit_reverse_reachable_root hc cover q cut hlast i.val
      (by omega) i.isLt

private noncomputable def cutSplitCompressedCoverHom (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (D : c.outsideGraph.ConnectedComponent) :
    (cover D).multigraph.underlying →g
      (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying where
  toFun := id
  map_rel' := by
    intro u v huv
    obtain ⟨e, he⟩ := (cover D).multigraph.underlying_adj.mp huv
    let edge := c.cutCoverEdge cover q cut D e
    apply (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying_adj.mpr
    refine ⟨Sum.inl ⟨edge, ?_⟩, ?_⟩
    · rintro ⟨⟨i, side⟩, hi⟩
      have hval := congrArg Subtype.val hi
      have hside : side = 0 ∨ side = 1 := by
        have hsval : side.val = 0 ∨ side.val = 1 := by omega
        exact hsval.imp Fin.ext Fin.ext
      rcases hside with rfl | rfl
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedOriginalEdge cover q (splitPartnerIndex cut.1 i.1.1) := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            cutSplitCycleTransition, EdgeIndexedMultigraph.ParallelPair.liftTransition,
            cutCoverEdge, cutOriginalEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedOriginalEdge] at hcycle
      · have hcycle : c.augmentedCoverEdge cover q D e =
            c.augmentedCopiedEdge cover q i.1.2 := by
          simpa [edge, EdgeIndexedMultigraph.transitionEdge,
            cutSplitCycleTransition, EdgeIndexedMultigraph.ParallelPair.liftTransition,
            cutCoverEdge, cutCopiedEdge] using hval.symm
        simp [augmentedCoverEdge, augmentedCopiedEdge] at hcycle
    · exact (c.cutAugmentedTrailMultigraph_ends_cover cover q cut D e).trans he

/-- Deleting the copied edge at the arc endpoint and compressing the remaining two-arc
transitions preserves connectedness. -/
private theorem cutSplitCompressedMultigraph_connected (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying.Connected := by
  exact c.connected_of_cycle_reachable_and_component_covers cover
    (c.cutSplitCompressedMultigraph hc cover q cut hlast).underlying
    (c.cutSplit_cycle_reachable_root hc cover q cut hlast)
    (c.cutSplitCompressedCoverHom hc cover q cut hlast) (by intros; rfl)

end Walk

end SimpleGraph

/-! ## CyclePreparedEuler -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- The compressed two-arc transition multigraph has an Euler circuit. -/
private theorem exists_split_compressed_eulerian [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] (k : Fin c.length)
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 0) :
    let q := c.cycleEulerizationCompletion hc cover
    let M := c.augmentedTrailMultigraph cover q
    let transition := c.splitCycleTransition hc cover q k hlast
    ∃ (u : V) (p : (M.compressTransitions transition).IndexedWalk u u),
      p.IsEulerian := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.augmentedTrailMultigraph cover q
  let transition := c.splitCycleTransition hc cover q k hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.splitCycleTransition_edge_injective hc cover q k hlast
  have heven : ∀ v, Even ((M.compressTransitions transition).degree v) := by
    intro v
    apply M.compressTransitions_even_degree transition hinj
    exact c.cycleEulerization_even_degree hc cover
  exact (M.compressTransitions transition).exists_indexedEulerian
    (c.splitCompressedMultigraph_connected hc cover q k hlast) heven

/-- The compressed closing-edge-cut transition multigraph has an Euler circuit. -/
private theorem exists_forwardLastCut_compressed_eulerian [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 1) :
    let q := c.cycleEulerizationCompletion hc cover
    let cut := lastActiveCycleCopy q hlast
    let M := c.cutAugmentedTrailMultigraph cover q cut
    let transition := c.forwardLastCutCycleTransition hc cover q hlast
    ∃ (u : V) (p : (M.compressTransitions transition).IndexedWalk u u),
      p.IsEulerian := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.forwardLastCutCycleTransition hc cover q hlast
  have hbase : ∀ v, Even (M.degree v) := by
    intro v
    apply (c.augmentedTrailMultigraph cover q).eraseParallelPair_even_degree
      (c.cycleParallelPair cover q cut.2)
    exact c.cycleEulerization_even_degree hc cover
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.forwardLastCutCycleTransition_edge_injective hc cover q hlast
  have heven : ∀ v, Even ((M.compressTransitions transition).degree v) := by
    intro v
    exact M.compressTransitions_even_degree transition hinj hbase v
  exact (M.compressTransitions transition).exists_indexedEulerian
    (c.forwardLastCutCompressedMultigraph_connected hc cover q hlast) heven

/-- The compressed distinguished-edge-cut transition multigraph has an Euler circuit. -/
private theorem exists_cutSplit_compressed_eulerian [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (cut : ActiveCycleCopy (c.cycleEulerizationCompletion hc cover))
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 0) :
    let q := c.cycleEulerizationCompletion hc cover
    let M := c.cutAugmentedTrailMultigraph cover q cut
    let transition := c.cutSplitCycleTransition hc cover q cut hlast
    ∃ (u : V) (p : (M.compressTransitions transition).IndexedWalk u u),
      p.IsEulerian := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  have hbase : ∀ v, Even (M.degree v) := by
    intro v
    apply (c.augmentedTrailMultigraph cover q).eraseParallelPair_even_degree
      (c.cycleParallelPair cover q cut.2)
    exact c.cycleEulerization_even_degree hc cover
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.cutSplitCycleTransition_edge_injective hc cover q cut hlast
  have heven : ∀ v, Even ((M.compressTransitions transition).degree v) := by
    intro v
    exact M.compressTransitions_even_degree transition hinj hbase v
  exact (M.compressTransitions transition).exists_indexedEulerian
    (c.cutSplitCompressedMultigraph_connected hc cover q cut hlast) heven

end Walk

end SimpleGraph

/-! ## IndexedEulerCircuit -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)

/-- The next position in a nonempty finite cyclic order. -/
private def cyclicNext (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The previous position in a nonempty finite cyclic order. -/
private def cyclicPrev (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

@[simp]
private theorem cyclicNext_prev (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicNext n hn (cyclicPrev n hn i) = i := by
  apply Fin.ext
  by_cases h : i.val = 0
  · simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    have hin : (i.val + n - 1) % n = n - 1 := by
      rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hin, show n - 1 + 1 = n by omega, Nat.mod_self, h]
  · simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    have hin : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hin, Nat.sub_add_cancel (Nat.pos_of_ne_zero h), Nat.mod_eq_of_lt i.isLt]

@[simp]
private theorem cyclicPrev_next (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicPrev n hn (cyclicNext n hn i) = i := by
  apply Fin.ext
  by_cases hlast : i.val + 1 = n
  · simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlt : i.val + 1 < n := by omega
    simp only [cyclicNext, cyclicPrev, Fin.val_mk]
    rw [Nat.mod_eq_of_lt hlt,
      show i.val + 1 + n - 1 = i.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt i.isLt]

/-- In a cyclic order of at least three positions, the predecessor and successor differ. -/
private theorem cyclicPrev_ne_next (n : ℕ) (hn : 0 < n) (hthree : 3 ≤ n)
    (i : Fin n) : cyclicPrev n hn i ≠ cyclicNext n hn i := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnext (j : Fin n) : cyclicNext n hn j = j + 1 := by
    apply Fin.ext
    simp [cyclicNext, Fin.val_add, Nat.mod_eq_of_lt (show 1 < n by omega)]
  intro h
  have htwo : i = cyclicNext n hn (cyclicNext n hn i) := by
    rw [← h, cyclicNext_prev]
  rw [hnext, hnext, add_assoc] at htwo
  have hcancel : i + 0 = i + ((1 : Fin n) + 1) := by simpa using htwo
  have hzero : (0 : Fin n) = (1 : Fin n) + 1 := add_left_cancel hcancel
  have hval := congrArg Fin.val hzero
  simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < n by omega)] at hval

/-- Away from zero, cyclic predecessor subtracts one from the underlying value. -/
private theorem cyclicPrev_val_of_ne_zero (n : ℕ) (hn : 0 < n)
    (i : Fin n) (hi : i.val ≠ 0) : (cyclicPrev n hn i).val = i.val - 1 := by
  simp only [cyclicPrev, Fin.val_mk]
  rw [show i.val + n - 1 = (i.val - 1) + n by
      have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
      omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A finite directed traversal of every edge identity around one circuit. -/
private structure CyclicCircuit where
  /-- Number of edge positions. -/
  size : ℕ
  size_pos : 0 < size
  /-- Vertex before the edge at a cyclic position. -/
  vertex : Fin size → V
  /-- Edge traversed from this position to the next one. -/
  edge : Fin size → E
  /-- The indexed edge has the displayed consecutive endpoints. -/
  ends_edge : ∀ i, M.ends (edge i) =
    s(vertex i, vertex (cyclicNext size size_pos i))
  /-- Every edge identity occurs exactly once. -/
  edge_bijective : Function.Bijective edge

namespace IndexedWalk

private theorem getVert_succ_fin {x : V} (p : M.IndexedWalk x x) (hne : p.edges ≠ [])
    (i : Fin p.edges.length) :
    p.toWalk.getVert (i.val + 1) =
      p.toWalk.getVert (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val := by
  by_cases hlt : i.val + 1 < p.edges.length
  · simp [cyclicNext, Nat.mod_eq_of_lt hlt]
  · have heq : i.val + 1 = p.edges.length := by omega
    have hlength : p.toWalk.length = p.edges.length := p.length_toWalk
    calc
      p.toWalk.getVert (i.val + 1) = x := by
        rw [heq, ← hlength, p.toWalk.getVert_length]
      _ = p.toWalk.getVert 0 := p.toWalk.getVert_zero.symm
      _ = p.toWalk.getVert
          (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val := by
        congr 1
        simp [cyclicNext, heq]

/-- An indexed Euler circuit with at least one edge gives a cyclic edge-position encoding. -/
private noncomputable def toCyclicCircuit [Nonempty E] {x : V}
    (p : M.IndexedWalk x x) (hp : p.IsEulerian) : M.CyclicCircuit := by
  classical
  have hne : p.edges ≠ [] := by
    let e : E := Classical.choice (inferInstance : Nonempty E)
    exact fun h ↦ by simpa [h] using hp.2 e
  refine {
    size := p.edges.length
    size_pos := List.length_pos_of_ne_nil hne
    vertex := fun i ↦ p.toWalk.getVert i.val
    edge := p.edges.get
    ends_edge := ?_
    edge_bijective := ?_ }
  · intro i
    have hi : i.val < p.toWalk.edges.length := by
      rw [p.toWalk.length_edges, p.length_toWalk]
      exact i.isLt
    have hedge := p.toWalk.getElem_edges hi
    have hmap : p.toWalk.edges[i.val]'hi = M.ends (p.edges[i.val]'i.isLt) := by
      simp only [p.edges_toWalk, List.getElem_map]
    calc
      M.ends (p.edges.get i) = p.toWalk.edges.get ⟨i.val, hi⟩ := hmap.symm
      _ = s(p.toWalk.getVert i.val, p.toWalk.getVert (i.val + 1)) := by
        simpa using hedge
      _ = s(p.toWalk.getVert i.val,
          p.toWalk.getVert
            (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val) :=
        congrArg (s(p.toWalk.getVert i.val, ·)) (getVert_succ_fin M p hne i)
  · constructor
    · exact hp.1.injective_get
    · intro e
      exact List.mem_iff_get.mp (hp.2 e)

end IndexedWalk

namespace CyclicCircuit

variable (C : M.CyclicCircuit)

/-- Add an offset to a cyclic position, using the circuit size as modulus. -/
private def rotatedPosition (start i : Fin C.size) : Fin C.size :=
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  start + i

/-- All cyclic positions, starting at a prescribed position. -/
private def rotatedPositions (start : Fin C.size) : List (Fin C.size) :=
  List.ofFn fun i ↦ C.rotatedPosition M start i

/-- The rotated list of cyclic positions has no repetitions. -/
private theorem rotatedPositions_nodup (start : Fin C.size) :
    (C.rotatedPositions M start).Nodup := by
  rw [rotatedPositions, List.nodup_ofFn]
  intro i j hij
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  apply add_left_cancel (a := start)
  exact hij

/-- Every cyclic position occurs in every rotated position list. -/
private theorem mem_rotatedPositions (start i : Fin C.size) :
    i ∈ C.rotatedPositions M start := by
  rw [rotatedPositions, List.mem_ofFn]
  let _ : NeZero C.size := ⟨Nat.ne_of_gt C.size_pos⟩
  exact ⟨(Equiv.addLeft start).symm i, (Equiv.addLeft start).apply_symm_apply i⟩

private theorem rotatedPosition_succ (start : Fin C.size) (i : ℕ)
    (hi : i + 1 < C.size) :
    C.rotatedPosition M start ⟨i + 1, hi⟩ =
      cyclicNext C.size C.size_pos
        (C.rotatedPosition M start ⟨i, by omega⟩) := by
  apply Fin.ext
  simp only [rotatedPosition, cyclicNext, Fin.val_mk, Fin.val_add]
  rw [Nat.mod_add_mod]
  congr 1

private theorem cyclicNext_rotatedPosition_last (start : Fin C.size) :
    cyclicNext C.size C.size_pos
        (C.rotatedPosition M start
          ⟨C.size - 1, by have := C.size_pos; omega⟩) = start := by
  apply Fin.ext
  simp only [rotatedPosition, cyclicNext, Fin.val_mk, Fin.val_add]
  rw [Nat.mod_add_mod,
    show start.val + (C.size - 1) + 1 = start.val + C.size by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt start.isLt]

/-- A cyclic position list with the initial position repeated at the end. -/
private def closedRotatedPosition (start : Fin C.size) (i : Fin (C.size + 1)) :
    Fin C.size :=
  if hi : i.val < C.size then C.rotatedPosition M start ⟨i.val, hi⟩ else start

/-- Consecutive entries in a closed rotation are consecutive cyclic positions. -/
private theorem closedRotatedPosition_succ (start : Fin C.size) (i : ℕ)
    (hi : i < C.size) :
    C.closedRotatedPosition M start ⟨i + 1, by omega⟩ =
      cyclicNext C.size C.size_pos
        (C.closedRotatedPosition M start ⟨i, by omega⟩) := by
  by_cases hnext : i + 1 < C.size
  · simp only [closedRotatedPosition, dite_eq_left hi, dite_eq_left hnext]
    exact C.rotatedPosition_succ M start i hnext
  · have hilast : i = C.size - 1 := by omega
    simp only [closedRotatedPosition, dite_eq_left hi, dite_eq_right hnext]
    subst i
    exact (C.cyclicNext_rotatedPosition_last M start).symm

/-- Vertices and pass marks in cyclic order, with the initial entry repeated at the end. -/
private def markedVertexListing (start : Fin C.size) (marked : Fin C.size → Bool) :
    List (V × Bool) :=
  List.ofFn fun i ↦
    let j := C.closedRotatedPosition M start i
    (C.vertex j, marked j)

/-- The closed marked listing is one turn of distinct positions followed by its start. -/
private theorem markedVertexListing_eq (start : Fin C.size)
    (marked : Fin C.size → Bool) :
    C.markedVertexListing M start marked =
      (C.rotatedPositions M start).map
        (fun i ↦ (C.vertex i, marked i)) ++
      [(C.vertex start, marked start)] := by
  rw [markedVertexListing, List.ofFn_succ', List.concat_eq_append,
    rotatedPositions, List.map_ofFn]
  congr 1
  · rw [List.ofFn_inj]
    funext i
    simp [closedRotatedPosition]
  · simp [closedRotatedPosition]

/-- A local cyclic step condition proves the chain condition for the closed marked listing. -/
private theorem markedVertexListing_isChain (start : Fin C.size)
    (marked : Fin C.size → Bool) (R : (V × Bool) → (V × Bool) → Prop)
    (hstep : ∀ i,
      R (C.vertex i, marked i)
        (C.vertex (cyclicNext C.size C.size_pos i),
          marked (cyclicNext C.size C.size_pos i))) :
    (C.markedVertexListing M start marked).IsChain R := by
  rw [markedVertexListing, List.isChain_ofFn]
  intro i hi
  have hi0 : i < C.size := by omega
  by_cases hnext : i + 1 < C.size
  · simp only [closedRotatedPosition, dite_eq_left hi0, dite_eq_left hnext]
    rw [C.rotatedPosition_succ M start i hnext]
    exact hstep _
  · have hilast : i = C.size - 1 := by omega
    simp only [closedRotatedPosition, dite_eq_left hi0, dite_eq_right hnext]
    have hpos : C.rotatedPosition M start ⟨i, hi0⟩ =
        C.rotatedPosition M start
          ⟨C.size - 1, by have := C.size_pos; omega⟩ := by
      congr
    rw [hpos]
    simpa only [C.cyclicNext_rotatedPosition_last M start] using
      hstep (C.rotatedPosition M start
        ⟨C.size - 1, by have := C.size_pos; omega⟩)

/-- Keep an unmarked cyclic occurrence and discard a marked occurrence. -/
private def keptVertex (marked : Fin C.size → Bool) (i : Fin C.size) : Option V :=
  if marked i then none else some (C.vertex i)

/-- The unmarked vertices in one nonrepeating turn around the circuit. -/
private def keptCoreVertices (start : Fin C.size) (marked : Fin C.size → Bool) :
    List V :=
  (C.rotatedPositions M start).filterMap (C.keptVertex M marked)

/-- The unmarked cyclic listing, closed by repeating its initial vertex. -/
private def keptVertexListing (start : Fin C.size) (marked : Fin C.size → Bool) :
    List V :=
  C.keptCoreVertices M start marked ++ [C.vertex start]

private theorem keptCoreVertices_nodup (start : Fin C.size)
    (marked : Fin C.size → Bool)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) :
    (C.keptCoreVertices M start marked).Nodup := by
  rw [keptCoreVertices]
  apply C.rotatedPositions_nodup M start |>.filterMap
  intro i j z hzi hzj
  cases hi : marked i with
  | true => simp [keptVertex, hi] at hzi
  | false =>
      cases hj : marked j with
      | true => simp [keptVertex, hj] at hzj
      | false =>
          have hvi : C.vertex i = z := by simpa [keptVertex, hi] using hzi
          have hvj : C.vertex j = z := by simpa [keptVertex, hj] using hzj
          exact (hunique z).unique ⟨hvi, hi⟩ ⟨hvj, hj⟩

private theorem mem_keptCoreVertices (start : Fin C.size)
    (marked : Fin C.size → Bool)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) (z : V) :
    z ∈ C.keptCoreVertices M start marked := by
  obtain ⟨i, hi, _⟩ := hunique z
  rw [keptCoreVertices, List.mem_filterMap]
  exact ⟨i, C.mem_rotatedPositions M start i, by simp [keptVertex, hi]⟩

private theorem rotatedPositions_eq_cons_cons (start : Fin C.size)
    (hsize : 2 ≤ C.size) :
    ∃ l, C.rotatedPositions M start =
      start :: cyclicNext C.size C.size_pos start :: l := by
  have hlength : (C.rotatedPositions M start).length = C.size := by
    simp [rotatedPositions]
  have hget0 : (C.rotatedPositions M start)[0]? = some start := by
    change (List.ofFn fun i ↦ C.rotatedPosition M start i)[0]? = some start
    rw [List.getElem?_ofFn]
    simp only [dite_eq_left C.size_pos]
    congr 1
    apply Fin.ext
    simp [rotatedPosition, Fin.val_add, Nat.mod_eq_of_lt start.isLt]
  have hget1 : (C.rotatedPositions M start)[1]? =
      some (cyclicNext C.size C.size_pos start) := by
    change (List.ofFn fun i ↦ C.rotatedPosition M start i)[1]? = _
    rw [List.getElem?_ofFn]
    split
    · rename_i hone
      congr 1
    · omega
  cases hrot : C.rotatedPositions M start with
  | nil =>
      exfalso
      rw [hrot] at hlength
      simp at hlength
      omega
  | cons a l =>
      cases hl : l with
      | nil =>
          exfalso
          rw [hrot, hl] at hlength
          simp at hlength
          omega
      | cons b t =>
          rw [hrot, hl] at hget0 hget1
          have ha : a = start := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using hget0
          have hb : b = cyclicNext C.size C.size_pos start := by
            simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] using hget1
          rw [ha, hb]
          refine ⟨t, ?_⟩
          rfl

/-- If the start and its successor are unmarked, they begin the kept cyclic listing. -/
private theorem keptVertexListing_eq_root_next (start : Fin C.size)
    (marked : Fin C.size → Bool) (hsize : 2 ≤ C.size)
    (hstart : marked start = false)
    (hnext : marked (cyclicNext C.size C.size_pos start) = false) :
    ∃ l, C.keptVertexListing M start marked =
      C.vertex start :: C.vertex (cyclicNext C.size C.size_pos start) ::
        l ++ [C.vertex start] := by
  obtain ⟨l, hl⟩ := C.rotatedPositions_eq_cons_cons M start hsize
  refine ⟨l.filterMap (C.keptVertex M marked), ?_⟩
  rw [keptVertexListing, keptCoreVertices, hl]
  simp [keptVertex, hstart, hnext]

private theorem getLast_rotatedPositions (start : Fin C.size) :
    (C.rotatedPositions M start).getLast (by
      intro h
      have hlength := congrArg List.length h
      have hzero : C.size = 0 := by simpa [rotatedPositions] using hlength
      exact Nat.ne_of_gt C.size_pos hzero) =
      cyclicPrev C.size C.size_pos start := by
  have hfn : (List.ofFn fun i ↦ C.rotatedPosition M start i) ≠ [] := by
    intro h
    have hlength := congrArg List.length h
    have hzero : C.size = 0 := by simpa using hlength
    exact Nat.ne_of_gt C.size_pos hzero
  have hlast : (C.rotatedPositions M start).getLast (by
      simpa only [rotatedPositions] using hfn) =
      C.rotatedPosition M start
        ⟨C.size - 1, by have := C.size_pos; omega⟩ := by
    simpa only [rotatedPositions] using List.getLast_ofFn hfn
  rw [hlast]
  have hnext := C.cyclicNext_rotatedPosition_last M start
  have hprev := congrArg (cyclicPrev C.size C.size_pos) hnext
  rw [cyclicPrev_next] at hprev
  exact hprev

/-- If the start and its predecessor are unmarked, they end the kept cyclic listing. -/
private theorem keptVertexListing_eq_prev_root (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false)
    (hprev : marked (cyclicPrev C.size C.size_pos start) = false) :
    ∃ l, C.keptVertexListing M start marked =
      l ++ [C.vertex (cyclicPrev C.size C.size_pos start), C.vertex start] := by
  have hrot : C.rotatedPositions M start ≠ [] := by
    intro h
    have hlength := congrArg List.length h
    have hzero : C.size = 0 := by simpa [rotatedPositions] using hlength
    exact Nat.ne_of_gt C.size_pos hzero
  have hcore : C.keptCoreVertices M start marked ≠ [] := by
    have hmem : C.vertex start ∈ C.keptCoreVertices M start marked := by
      rw [keptCoreVertices, List.mem_filterMap]
      exact ⟨start, C.mem_rotatedPositions M start start,
        by simp [keptVertex, hstart]⟩
    exact List.ne_nil_of_mem hmem
  have hlast : (C.keptCoreVertices M start marked).getLast hcore =
      C.vertex (cyclicPrev C.size C.size_pos start) := by
    change ((C.rotatedPositions M start).filterMap
      (C.keptVertex M marked)).getLast _ = _
    apply List.getLast_filterMap_of_eq_some hrot
    rw [C.getLast_rotatedPositions M start]
    simp [keptVertex, hprev]
  let core := C.keptCoreVertices M start marked
  have hdecomp : core.dropLast ++
      [C.vertex (cyclicPrev C.size C.size_pos start)] = core := by
    simpa only [core, hlast] using List.dropLast_append_getLast hcore
  refine ⟨core.dropLast, ?_⟩
  rw [keptVertexListing]
  calc
    C.keptCoreVertices M start marked ++ [C.vertex start] =
        (core.dropLast ++
          [C.vertex (cyclicPrev C.size C.size_pos start)]) ++
          [C.vertex start] := congrArg (· ++ [C.vertex start]) hdecomp.symm
    _ = core.dropLast ++
        [C.vertex (cyclicPrev C.size C.size_pos start), C.vertex start] := by simp

private theorem keptCoreVertices_eq_cons (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) :
    ∃ l, C.keptCoreVertices M start marked = C.vertex start :: l := by
  have hrot : C.rotatedPositions M start ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    have hzero : C.size = 0 := by
      simpa only [rotatedPositions, List.length_ofFn, List.length_nil] using hlength
    exact Nat.ne_of_gt C.size_pos hzero
  have hrotHead : (C.rotatedPositions M start).head hrot = start := by
    have hfn : (List.ofFn fun i ↦ C.rotatedPosition M start i) ≠ [] := by
      simpa only [rotatedPositions] using hrot
    calc
      (C.rotatedPositions M start).head hrot =
          C.rotatedPosition M start ⟨0, C.size_pos⟩ := by
        simpa only [rotatedPositions] using List.head_ofFn hfn
      _ = start := by
        apply Fin.ext
        simp [rotatedPosition, Fin.val_add, Nat.mod_eq_of_lt start.isLt]
  have hcore : C.keptCoreVertices M start marked ≠ [] := by
    exact List.ne_nil_of_mem (C.mem_keptCoreVertices M start marked hunique (C.vertex start))
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hcore
  have hhead : (C.keptCoreVertices M start marked).head hcore = C.vertex start := by
    change ((C.rotatedPositions M start).filterMap
      (C.keptVertex M marked)).head _ = C.vertex start
    apply List.head_filterMap_of_eq_some hrot
    rw [hrotHead]
    simp [keptVertex, hstart]
  have ha : a = C.vertex start := by
    simpa [hal] using hhead
  subst a
  exact ⟨l, hal⟩

/-- Apart from the repeated closing root, the kept cyclic listing has no repetitions. -/
private theorem keptVertexListing_tail_nodup (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) :
    (C.keptVertexListing M start marked).tail.Nodup := by
  obtain ⟨l, hl⟩ := C.keptCoreVertices_eq_cons M start marked hstart hunique
  have hn := C.keptCoreVertices_nodup M start marked hunique
  rw [keptVertexListing, hl, List.cons_append, List.tail_cons]
  rw [hl] at hn
  have hn' := List.nodup_cons.mp hn
  rw [List.nodup_append]
  refine ⟨hn'.2, List.nodup_singleton _, ?_⟩
  intro z hz z' hz'
  rw [List.mem_singleton] at hz'
  subst z'
  exact fun h ↦ hn'.1 (h ▸ hz)

/-- Every vertex occurs in the noninitial part of the kept cyclic listing. -/
private theorem mem_tail_keptVertexListing (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) (z : V) :
    z ∈ (C.keptVertexListing M start marked).tail := by
  obtain ⟨l, hl⟩ := C.keptCoreVertices_eq_cons M start marked hstart hunique
  have hz := C.mem_keptCoreVertices M start marked hunique z
  rw [keptVertexListing, hl, List.cons_append, List.tail_cons]
  by_cases hroot : z = C.vertex start
  · subst z
    simp
  · rw [hl, List.mem_cons] at hz
    exact List.mem_append_left _ (hz.resolve_left hroot)

/-- The edge entering a cyclic position. -/
private def incoming (i : Fin C.size) : E :=
  C.edge (cyclicPrev C.size C.size_pos i)

@[simp]
private theorem ends_incoming (i : Fin C.size) :
    M.ends (incoming M C i) =
      s(C.vertex (cyclicPrev C.size C.size_pos i), C.vertex i) := by
  rw [incoming, C.ends_edge, cyclicNext_prev]

/-- A pass is kept when its designated anchor is one of its two incident tour edges. -/
private def Keeps (anchor : V → E) (i : Fin C.size) : Prop :=
  incoming M C i = anchor (C.vertex i) ∨ C.edge i = anchor (C.vertex i)

/-- Mark every pass except the pass containing the designated anchor edge. -/
private noncomputable def anchorMarked (anchor : V → E) (i : Fin C.size) : Bool :=
  by
    classical
    exact decide (¬Keeps M C anchor i)

/-- An incident anchor selects exactly one cyclic pass through its vertex. -/
private theorem existsUnique_keeps (anchor : V → E)
    (hinc : ∀ z, M.Inc z (anchor z)) (z : V) :
    ∃! i, C.vertex i = z ∧ Keeps M C anchor i := by
  classical
  have hatMost : ∀ i j,
      C.vertex i = z ∧ Keeps M C anchor i →
      C.vertex j = z ∧ Keeps M C anchor j → i = j := by
    intro i j hi hj
    rcases hi with ⟨hiv, hiin | hiout⟩
    <;> rcases hj with ⟨hjv, hjin | hjout⟩
    · have hedge : cyclicPrev C.size C.size_pos i =
          cyclicPrev C.size C.size_pos j := by
        apply C.edge_bijective.1
        calc
          C.edge (cyclicPrev C.size C.size_pos i) = anchor (C.vertex i) := hiin
          _ = anchor (C.vertex j) := congrArg anchor (hiv.trans hjv.symm)
          _ = C.edge (cyclicPrev C.size C.size_pos j) := hjin.symm
      have := congrArg (cyclicNext C.size C.size_pos) hedge
      simpa using this
    · have hedge : cyclicPrev C.size C.size_pos i = j := by
        apply C.edge_bijective.1
        calc
          C.edge (cyclicPrev C.size C.size_pos i) = anchor (C.vertex i) := hiin
          _ = anchor (C.vertex j) := congrArg anchor (hiv.trans hjv.symm)
          _ = C.edge j := hjout.symm
      have hij : i = cyclicNext C.size C.size_pos j := by
        calc
          i = cyclicNext C.size C.size_pos
              (cyclicPrev C.size C.size_pos i) :=
            (cyclicNext_prev C.size C.size_pos i).symm
          _ = cyclicNext C.size C.size_pos j := congrArg _ hedge
      exfalso
      apply M.loopless (C.edge j) z
      rw [C.ends_edge, hjv, ← hij, hiv]
    · have hedge : i = cyclicPrev C.size C.size_pos j := by
        apply C.edge_bijective.1
        calc
          C.edge i = anchor (C.vertex i) := hiout
          _ = anchor (C.vertex j) := congrArg anchor (hiv.trans hjv.symm)
          _ = C.edge (cyclicPrev C.size C.size_pos j) := hjin.symm
      have hji : j = cyclicNext C.size C.size_pos i := by
        calc
          j = cyclicNext C.size C.size_pos
              (cyclicPrev C.size C.size_pos j) :=
            (cyclicNext_prev C.size C.size_pos j).symm
          _ = cyclicNext C.size C.size_pos i := congrArg _ hedge.symm
      exfalso
      apply M.loopless (C.edge i) z
      rw [C.ends_edge, hiv, ← hji, hjv]
    · apply C.edge_bijective.1
      exact hiout.trans ((congrArg anchor (hiv.trans hjv.symm)).trans hjout.symm)
  obtain ⟨j, hj⟩ := C.edge_bijective.2 (anchor z)
  have hzends : z ∈ s(C.vertex j,
      C.vertex (cyclicNext C.size C.size_pos j)) := by
    rw [← C.ends_edge, hj]
    exact hinc z
  rcases Sym2.mem_iff.mp hzends with hzj | hznext
  · refine ⟨j, ⟨hzj.symm, Or.inr ?_⟩, ?_⟩
    · simpa [hzj] using hj
    · intro i hi
      exact hatMost i j hi ⟨hzj.symm, Or.inr (by simpa [hzj] using hj)⟩
  · let i := cyclicNext C.size C.size_pos j
    have hiv : C.vertex i = z := hznext.symm
    have hiin : incoming M C i = anchor (C.vertex i) := by
      rw [incoming, cyclicPrev_next, hj, hiv]
    refine ⟨i, ⟨hiv, Or.inl hiin⟩, ?_⟩
    intro k hk
    exact hatMost k i hk ⟨hiv, Or.inl hiin⟩

/-- Each vertex has exactly one unmarked pass under anchor marking. -/
private theorem existsUnique_anchorMarked (anchor : V → E)
    (hinc : ∀ z, M.Inc z (anchor z)) (z : V) :
    ∃! i, C.vertex i = z ∧ anchorMarked M C anchor i = false := by
  classical
  simpa [anchorMarked] using C.existsUnique_keeps M anchor hinc z

end CyclicCircuit

end EdgeIndexedMultigraph

end SimpleGraph

/-! ## SquareShortcut marking -/

namespace SimpleGraph

/-- Consecutive tagged vertices are compatible with shortcutting exactly the marked ones. -/
private def MarkedSquareStep {V : Type*} (G : SimpleGraph V)
    (a b : V × Bool) : Prop :=
  match a.2, b.2 with
  | false, false => G.square.Adj a.1 b.1
  | false, true => G.Adj a.1 b.1
  | true, false => G.Adj a.1 b.1
  | true, true => False

/-- Remove marked occurrences and forget the tags. -/
private def unmarkedVertices {V : Type*} : List (V × Bool) → List V
  | [] => []
  | (v, false) :: l => v :: unmarkedVertices l
  | (_, true) :: l => unmarkedVertices l

/-- A marked middle occurrence never has equal neighbors. -/
private def MarkedNoBacktrack {V : Type*} : List (V × Bool) → Prop
  | a :: b :: c :: l => (b.2 = true → a.1 ≠ c.1) ∧ MarkedNoBacktrack (b :: c :: l)
  | _ => True

private theorem MarkedNoBacktrack.tail {V : Type*} {a : V × Bool}
    {l : List (V × Bool)} (h : MarkedNoBacktrack (a :: l)) :
    MarkedNoBacktrack l := by
  cases l with
  | nil => trivial
  | cons b l =>
      cases l with
      | nil => trivial
      | cons c l => exact h.2

/-- Removing isolated marked occurrences from a compatible chain leaves a chain in the graph
square. -/
private theorem MarkedSquareStep.isChain_unmarkedVertices {V : Type*} {G : SimpleGraph V}
    {l : List (V × Bool)} (hl : l.IsChain (MarkedSquareStep G))
    (hn : MarkedNoBacktrack l) :
    (unmarkedVertices l).IsChain G.square.Adj := by
  induction l with
  | nil => simp [unmarkedVertices]
  | cons a l ih =>
      cases a with
      | mk u marked =>
          cases marked with
          | false =>
              cases l with
              | nil => simp [unmarkedVertices]
              | cons b l =>
                  cases b with
                  | mk v marked' =>
                      have hparts := List.isChain_cons_cons.mp hl
                      cases marked' with
                      | false =>
                          rw [unmarkedVertices, unmarkedVertices]
                          apply List.isChain_cons_cons.mpr
                          exact ⟨hparts.1, ih hparts.2 hn.tail⟩
                      | true =>
                          cases l with
                          | nil => simp [unmarkedVertices]
                          | cons d l =>
                              cases d with
                              | mk w marked'' =>
                                  have hparts' := List.isChain_cons_cons.mp hparts.2
                                  cases marked'' with
                                  | false =>
                                      rw [unmarkedVertices, unmarkedVertices,
                                        unmarkedVertices]
                                      apply List.isChain_cons_cons.mpr
                                      refine ⟨⟨hn.1 rfl,
                                        Or.inr ⟨v, hparts.1, hparts'.1⟩⟩, ?_⟩
                                      exact ih hparts.2 hn.tail
                                  | true =>
                                      exact False.elim (by
                                        simpa [MarkedSquareStep] using hparts'.1)
          | true =>
              rw [unmarkedVertices]
              exact ih (List.IsChain.tail hl) hn.tail

end SimpleGraph

/-! ## EulerCircuitMarking -/


namespace SimpleGraph

namespace EdgeIndexedMultigraph

namespace CyclicCircuit

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)

private theorem unmarkedVertices_map_positions (marked : Fin C.size → Bool)
    (positions : List (Fin C.size)) :
    unmarkedVertices
        (positions.map fun i ↦ (C.vertex i, marked i)) =
      positions.filterMap (C.keptVertex M marked) := by
  induction positions with
  | nil => rfl
  | cons i positions ih =>
      cases hi : marked i <;> simp [unmarkedVertices, keptVertex, hi, ih]

private theorem unmarkedVertices_append {l₁ l₂ : List (V × Bool)} :
    unmarkedVertices (l₁ ++ l₂) =
      unmarkedVertices l₁ ++ unmarkedVertices l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih =>
      rcases a with ⟨a, marked⟩
      cases marked <;> simp [unmarkedVertices, ih]

/-- Removing marked entries from the closed marked circuit gives its kept vertex listing. -/
private theorem unmarkedVertices_markedVertexListing (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false) :
    unmarkedVertices (C.markedVertexListing M start marked) =
      C.keptVertexListing M start marked := by
  rw [C.markedVertexListing_eq M start marked, unmarkedVertices_append,
    unmarkedVertices_map_positions, keptVertexListing, keptCoreVertices]
  simp [unmarkedVertices, hstart]

/-- At a degree-two vertex, every circuit pass contains any prescribed incident edge. -/
private theorem keeps_of_degree_eq_two (anchor : V → E)
    (hinc : ∀ z, M.Inc z (anchor z)) (i : Fin C.size)
    (hdegree : M.degree (C.vertex i) = 2) : C.Keeps M anchor i := by
  let incidence : Set E := {e | M.Inc (C.vertex i) e}
  have hincoming : C.incoming M i ∈ incidence := by
    simp [incidence, EdgeIndexedMultigraph.Inc]
  have houtgoing : C.edge i ∈ incidence := by
    simp [incidence, EdgeIndexedMultigraph.Inc, C.ends_edge]
  have hedges_ne : C.incoming M i ≠ C.edge i := by
    intro hedges
    have hpositions : cyclicPrev C.size C.size_pos i = i := by
      apply C.edge_bijective.1
      simpa only [incoming] using hedges
    have hnext : cyclicNext C.size C.size_pos i = i := by
      have h := congrArg (cyclicNext C.size C.size_pos) hpositions
      simpa using h.symm
    apply M.loopless (C.edge i) (C.vertex i)
    rw [C.ends_edge, hnext]
  have hincidence_card : incidence.ncard = 2 := by
    simpa [incidence, EdgeIndexedMultigraph.degree] using hdegree
  have hincidence_finite : incidence.Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hpair : ({C.incoming M i, C.edge i} : Set E) = incidence := by
    apply Set.eq_of_subset_of_ncard_le _ _ hincidence_finite
    · intro e he
      rcases Set.mem_insert_iff.mp he with rfl | he
      · exact hincoming
      · simpa using he ▸ houtgoing
    · rw [hincidence_card, Set.ncard_pair hedges_ne]
  have hanchor : anchor (C.vertex i) ∈ ({C.incoming M i, C.edge i} : Set E) := by
    rw [hpair]
    exact hinc (C.vertex i)
  rcases Set.mem_insert_iff.mp hanchor with h | h
  · exact Or.inl h.symm
  · exact Or.inr (Set.mem_singleton_iff.mp h).symm

/-- Anchor marking never deletes a pass through a degree-two vertex. -/
private theorem anchorMarked_eq_false_of_degree_eq_two (anchor : V → E)
    (hinc : ∀ z, M.Inc z (anchor z)) (i : Fin C.size)
    (hdegree : M.degree (C.vertex i) = 2) :
    C.anchorMarked M anchor i = false := by
  simp [anchorMarked, C.keeps_of_degree_eq_two M anchor hinc i hdegree]

private theorem noBacktrack_of_getElem (l : List (V × Bool))
    (hlocal : ∀ (i : ℕ) (hi : i + 2 < l.length),
      l[i + 1].2 = true → l[i].1 ≠ l[i + 2].1) :
    MarkedNoBacktrack l := by
  match l with
  | a :: b :: c :: t =>
      constructor
      · intro hb
        simpa using hlocal 0 (by simp) hb
      · apply noBacktrack_of_getElem (b :: c :: t)
        intro i hi hb
        have h := hlocal (i + 1) (by simpa using hi) hb
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | [] => trivial
  | [_] => trivial
  | [_, _] => trivial
termination_by l.length

/-- Three vertices with distinct selected passes require at least three circuit positions. -/
private theorem three_le_size_of_unique_unmarked [Fintype V]
    (marked : Fin C.size → Bool)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
    (hcard : 3 ≤ Fintype.card V) : 3 ≤ C.size := by
  classical
  let position : V → Fin C.size := fun z ↦ Classical.choose (hunique z)
  have hposition (z : V) :
      C.vertex (position z) = z ∧ marked (position z) = false :=
    (Classical.choose_spec (hunique z)).1
  have hposition_injective : Function.Injective position := by
    intro z w hzw
    exact (hposition z).1.symm.trans
      ((congrArg C.vertex hzw).trans (hposition w).1)
  have hle : Fintype.card V ≤ Fintype.card (Fin C.size) :=
    Fintype.card_le_of_injective position hposition_injective
  simpa using hcard.trans hle

/-- If every circuit edge has an unmarked endpoint and every vertex has a unique unmarked
pass, then no marked pass immediately backtracks. -/
private theorem markedVertexListing_noBacktrack [Fintype V]
    (start : Fin C.size) (marked : Fin C.size → Bool)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
    (hedge : ∀ i, marked i = false ∨
      marked (cyclicNext C.size C.size_pos i) = false)
    (hcard : 3 ≤ Fintype.card V) :
    MarkedNoBacktrack (C.markedVertexListing M start marked) := by
  classical
  have hsize := C.three_le_size_of_unique_unmarked M marked hunique hcard
  have hpass (i : Fin C.size) (hi : marked i = true) :
      C.vertex (cyclicPrev C.size C.size_pos i) ≠
        C.vertex (cyclicNext C.size C.size_pos i) := by
    have hiprev : marked (cyclicPrev C.size C.size_pos i) = false := by
      rcases hedge (cyclicPrev C.size C.size_pos i) with h | h
      · exact h
      · rw [cyclicNext_prev] at h
        simp [hi] at h
    have hinext : marked (cyclicNext C.size C.size_pos i) = false := by
      rcases hedge i with h | h
      · simp [hi] at h
      · exact h
    intro heq
    have hpositions := (hunique
      (C.vertex (cyclicPrev C.size C.size_pos i))).unique
      ⟨rfl, hiprev⟩ ⟨heq.symm, hinext⟩
    exact cyclicPrev_ne_next C.size C.size_pos hsize i hpositions
  apply noBacktrack_of_getElem
  intro i hi hmarked
  have hlength :
      (C.markedVertexListing M start marked).length = C.size + 1 := by
    simp [markedVertexListing]
  have hi0 : i < C.size := by omega
  have hi1 : i + 1 < C.size := by omega
  let p0 := C.closedRotatedPosition M start ⟨i, by omega⟩
  let p1 := C.closedRotatedPosition M start ⟨i + 1, by omega⟩
  let p2 := C.closedRotatedPosition M start ⟨i + 2, by omega⟩
  have hp01 : p1 = cyclicNext C.size C.size_pos p0 :=
    C.closedRotatedPosition_succ M start i hi0
  have hp12 : p2 = cyclicNext C.size C.size_pos p1 := by
    simpa only [p1, p2, Nat.add_assoc, Nat.reduceAdd] using
      C.closedRotatedPosition_succ M start (i + 1) hi1
  have hp0 : p0 = cyclicPrev C.size C.size_pos p1 := by
    rw [hp01, cyclicPrev_next]
  have hmarked' : marked p1 = true := by
    simpa only [markedVertexListing, List.getElem_ofFn, p1] using hmarked
  have hne := hpass p1 hmarked'
  simpa only [markedVertexListing, List.getElem_ofFn, p0, p2, hp0, hp12] using hne

/-- Data ensuring that deleting the marked passes of a cyclic Euler circuit gives a rooted
Hamiltonian cycle in the square. -/
private structure SquareMarking [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) where
  start : Fin C.size
  root_start : C.vertex start = root
  marked : Fin C.size → Bool
  start_unmarked : marked start = false
  unique_unmarked : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false
  two_le_size : 2 ≤ C.size
  three_le_card : 3 ≤ Fintype.card V
  marked_square_chain :
    (C.markedVertexListing M start marked).IsChain (MarkedSquareStep G)
  no_backtrack : MarkedNoBacktrack (C.markedVertexListing M start marked)
  next_unmarked : marked (cyclicNext C.size C.size_pos start) = false
  prev_unmarked : marked (cyclicPrev C.size C.size_pos start) = false
  next_adj : G.Adj root (C.vertex (cyclicNext C.size C.size_pos start))
  prev_adj : G.Adj (C.vertex (cyclicPrev C.size C.size_pos start)) root

/-- Local edge conditions package a marking into the data needed for square shortcutting. -/
private noncomputable def SquareMarking.ofLocal [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (start : Fin C.size)
    (marked : Fin C.size → Bool) (hroot : C.vertex start = root)
    (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false)
    (hedge : ∀ i, marked i = false ∨
      marked (cyclicNext C.size C.size_pos i) = false)
    (hsquare : ∀ i, G.square.Adj (C.vertex i)
      (C.vertex (cyclicNext C.size C.size_pos i)))
    (horiginal : ∀ i, marked i = true ∨
      marked (cyclicNext C.size C.size_pos i) = true →
        G.Adj (C.vertex i) (C.vertex (cyclicNext C.size C.size_pos i)))
    (hnext : marked (cyclicNext C.size C.size_pos start) = false)
    (hprev : marked (cyclicPrev C.size C.size_pos start) = false)
    (hnextAdj : G.Adj root
      (C.vertex (cyclicNext C.size C.size_pos start)))
    (hprevAdj : G.Adj
      (C.vertex (cyclicPrev C.size C.size_pos start)) root)
    (hcard : 3 ≤ Fintype.card V) : C.SquareMarking M G root := by
  classical
  have hsize := C.three_le_size_of_unique_unmarked M marked hunique hcard
  refine {
    start := start
    root_start := hroot
    marked := marked
    start_unmarked := hstart
    unique_unmarked := hunique
    two_le_size := by omega
    three_le_card := hcard
    marked_square_chain := ?_
    no_backtrack := C.markedVertexListing_noBacktrack M start marked
      hunique hedge hcard
    next_unmarked := hnext
    prev_unmarked := hprev
    next_adj := hnextAdj
    prev_adj := hprevAdj }
  apply C.markedVertexListing_isChain M
  intro i
  let j := cyclicNext C.size C.size_pos i
  cases hi : marked i <;> cases hj : marked j
  · simpa [MarkedSquareStep, j, hi, hj] using hsquare i
  · simpa [MarkedSquareStep, j, hi, hj] using
      horiginal i (Or.inr hj)
  · simpa [MarkedSquareStep, j, hi, hj] using
      horiginal i (Or.inl hi)
  · rcases hedge i with h | h
    · simp [hi] at h
    · simp [j, hj] at h

/-- A compatible square marking produces the rooted cyclic listing obtained by lifting every
marked pass. -/
private noncomputable def SquareMarking.toStrongSquareCycleListing
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V}
    (K : C.SquareMarking M G root) : G.StrongSquareCycleListing root := by
  classical
  let l := C.keptVertexListing M K.start K.marked
  let frontExists := C.keptVertexListing_eq_root_next M K.start K.marked
    K.two_le_size K.start_unmarked K.next_unmarked
  let middle := Classical.choose frontExists
  have hfront := Classical.choose_spec frontExists
  let backExists := C.keptVertexListing_eq_prev_root M K.start K.marked
    K.start_unmarked K.prev_unmarked
  let initial := Classical.choose backExists
  have hback := Classical.choose_spec backExists
  have hfront' : l = C.vertex K.start ::
      C.vertex (cyclicNext C.size C.size_pos K.start) ::
        middle ++ [C.vertex K.start] := by
    simpa only [l, middle] using hfront
  have hback' : l = initial ++
      [C.vertex (cyclicPrev C.size C.size_pos K.start), C.vertex K.start] := by
    simpa only [l, initial] using hback
  have htailNodup : l.tail.Nodup :=
    C.keptVertexListing_tail_nodup M K.start K.marked
      K.start_unmarked K.unique_unmarked
  have hmem : ∀ z, z ∈ l.tail :=
    C.mem_tail_keptVertexListing M K.start K.marked
      K.start_unmarked K.unique_unmarked
  have htailFinset : l.tail.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    exact List.mem_toFinset.mpr (hmem z)
  have htailLength : l.tail.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup htailNodup, htailFinset,
      Finset.card_univ]
  have hlength : l.length = l.tail.length + 1 := by
    rw [hfront']
    simp
  have hcard : 3 ≤ Fintype.card V := K.three_le_card
  have hfour : 4 ≤ l.length := by omega
  have hchain : l.IsChain G.square.Adj := by
    have h := MarkedSquareStep.isChain_unmarkedVertices
      K.marked_square_chain K.no_backtrack
    rw [C.unmarkedVertices_markedVertexListing M K.start K.marked
      K.start_unmarked] at h
    exact h
  refine {
    vertices := l
    first := C.vertex (cyclicNext C.size C.size_pos K.start)
    last := C.vertex (cyclicPrev C.size C.size_pos K.start)
    frontRest := middle ++ [C.vertex K.start]
    backRest := initial
    front_shape := by simpa [K.root_start] using hfront'
    back_shape := by simpa only [K.root_start] using hback'
    four_le_length := hfour
    square_chain := hchain
    tail_nodup := htailNodup
    mem_tail := hmem
    first_adj := K.next_adj
    last_adj := K.prev_adj }

/-- A compatible square marking lifts to a rooted Hamiltonian cycle in the square. -/
private theorem SquareMarking.toHasStrongSquareCycle
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V}
    (K : C.SquareMarking M G root) : G.HasStrongSquareCycle root :=
  K.toStrongSquareCycleListing.toHasStrongSquareCycle

end CyclicCircuit

end EdgeIndexedMultigraph

end SimpleGraph

/-! ## CycleEulerMarking -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- Prescribed incident edges on a cycle extend to incident anchors at every vertex when the
off-cycle vertices have degree two. -/
private theorem IsCycle.exists_incident_anchor {E : Type*} {c : G.Walk x x}
    (hc : c.IsCycle) (M : EdgeIndexedMultigraph V E)
    (cycleAnchor : Fin c.length → E)
    (hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i))
    (hdegree : ∀ v ∉ c.support, M.degree v = 2) :
    ∃ anchor : V → E, (∀ v, M.Inc v (anchor v)) ∧
      ∀ i : Fin c.length, anchor (c.getVert i) = cycleAnchor i := by
  classical
  have houtside (v : V) (hv : v ∉ c.support) : ∃ e, M.Inc v e := by
    let incidence : Set E := {e | M.Inc v e}
    have hcard : incidence.ncard = 2 := by
      simpa [incidence, EdgeIndexedMultigraph.degree] using hdegree v hv
    have hne : incidence.ncard ≠ 0 := by rw [hcard]; omega
    exact Set.nonempty_of_ncard_ne_zero hne
  let cycleIndex (v : V) (hv : v ∈ c.support) : Fin c.length :=
    hc.finLengthEquivSupport.symm ⟨v, hv⟩
  let anchor : V → E := fun v ↦
    if hv : v ∈ c.support then cycleAnchor (cycleIndex v hv)
    else Classical.choose (houtside v hv)
  refine ⟨anchor, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ c.support
    · have hindex : c.getVert (cycleIndex v hv) = v := by
        have heq := hc.finLengthEquivSupport.apply_symm_apply ⟨v, hv⟩
        have hval := congrArg Subtype.val heq
        rw [hc.finLengthEquivSupport_apply] at hval
        exact hval
      simp only [anchor, dite_eq_left hv]
      have h := hcycleInc (cycleIndex v hv)
      simpa only [hindex] using h
    · simp only [anchor, dite_eq_right hv]
      exact Classical.choose_spec (houtside v hv)
  · intro i
    have hmem : c.getVert i ∈ c.support := c.getVert_mem_support i
    have hindex : cycleIndex (c.getVert i) hmem = i := by
      apply hc.finLengthEquivSupport.injective
      rw [hc.finLengthEquivSupport.apply_symm_apply]
      apply Subtype.ext
      exact (hc.finLengthEquivSupport_apply i).symm
    simp [anchor, hmem, hindex]

/-- Every edge of an augmented trail multigraph is an edge of the original graph square. -/
private theorem augmentedTrailMultigraph_square_adj
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (e : c.AugmentedTrailEdge cover q) :
    (c.augmentedTrailMultigraph cover q).ends e ∈ G.square.edgeSet := by
  cases e with
  | inl e => exact c.trailSystemMultigraph_square_adj cover e
  | inr e =>
      have hadj : G.Adj (c.getVert e.1) (c.getVert (e.1.val + 1)) :=
        c.adj_getVert_succ e.1.isLt
      exact G.square.mem_edgeSet.mpr ⟨G.ne_of_adj hadj, Or.inl hadj⟩

/-- An augmented trail edge incident with the base cycle is an original graph edge. -/
private theorem augmentedTrailMultigraph_cycle_edge
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (e : c.AugmentedTrailEdge cover q) (a b : V)
    (he : (c.augmentedTrailMultigraph cover q).ends e = s(a, b))
    (hcycle : a ∈ c.support ∨ b ∈ c.support) : G.Adj a b := by
  cases e with
  | inl e => exact c.trailSystemMultigraph_cycle_edge cover e a b he hcycle
  | inr e =>
      apply G.mem_edgeSet.mp
      rw [← he]
      exact c.cycleCopyMultigraph_mem_edgeSet q e

/-- Every surviving edge after deleting a parallel cycle pair remains a square edge. -/
private theorem cutAugmentedTrailMultigraph_square_adj
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut) :
    (c.cutAugmentedTrailMultigraph cover q cut).ends e ∈ G.square.edgeSet :=
  c.augmentedTrailMultigraph_square_adj cover q e.1

/-- A surviving cut edge incident with the base cycle is an original graph edge. -/
private theorem cutAugmentedTrailMultigraph_cycle_edge
    (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut)
    (a b : V)
    (he : (c.cutAugmentedTrailMultigraph cover q cut).ends e = s(a, b))
    (hcycle : a ∈ c.support ∨ b ∈ c.support) : G.Adj a b :=
  c.augmentedTrailMultigraph_cycle_edge cover q e.1 a b he hcycle

/-- Vertices outside the base cycle retain degree two after parity correction. -/
private theorem augmentedTrailMultigraph_degree_eq_two_of_not_mem [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    {v : V} (hv : v ∉ c.support) :
    (c.augmentedTrailMultigraph cover q).degree v = 2 := by
  classical
  rw [augmentedTrailMultigraph, EdgeIndexedMultigraph.disjointSum_degree,
    c.trailSystemMultigraph_degree_eq_two cover hv,
    c.cycleCopyMultigraph_degree_eq_zero_of_not_mem hc q hv]

/-- If no copy leaves a bound cycle vertex, parity also excludes an incoming copy, so its
augmented degree is two. -/
private theorem augmentedTrailMultigraph_degree_eq_two_of_bound [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] (i : Fin c.length)
    (hbound : c.IsBoundVertex (c.getVert i))
    (hi : (c.cycleEulerizationCompletion hc cover).copies i = 0) :
    (c.cycleEulerizationMultigraph hc cover).degree (c.getVert i) = 2 := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  change q.copies i = 0 at hi
  have htrail :=
    c.trailSystemMultigraph_degree_eq_two_of_isBoundVertex hc cover i hbound
  have hprev : q.copies (i - 1) = 0 := by
    have heven : Even ((c.trailSystemMultigraph cover).degree (c.getVert i) +
        q.copies (i - 1) + q.copies i) := q.even_at i
    rw [htrail, hi] at heven
    obtain ⟨m, hm⟩ := heven
    have hlt := q.copies_lt_two (i - 1)
    omega
  rw [cycleEulerizationMultigraph, EdgeIndexedMultigraph.disjointSum_degree,
    htrail, c.cycleCopyMultigraph_degree_getVert hc, hprev, hi]

/-- Deleting a cycle-edge pair does not change the degree-two vertices off the cycle. -/
private theorem cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) {v : V} (hv : v ∉ c.support) :
    (c.cutAugmentedTrailMultigraph cover q cut).degree v = 2 := by
  let M := c.augmentedTrailMultigraph cover q
  let pair := c.cycleParallelPair cover q cut.2
  have hnot : ¬M.Inc v pair.first := by
    intro h
    change v ∈ s(c.getVert cut.1, c.getVert (cut.1 + 1)) at h
    rcases Sym2.mem_iff.mp h with h | h
    · exact hv (h ▸ c.getVert_mem_support cut.1)
    · exact hv (h ▸ c.getVert_mem_support (cut.1 + 1))
  rw [cutAugmentedTrailMultigraph]
  exact (M.eraseParallelPair_degree_eq_of_not_inc pair v hnot).trans
    (c.augmentedTrailMultigraph_degree_eq_two_of_not_mem hc cover q hv)

/-- The cycle-edge index anchored at a vertex when the two arcs from zero to `k` are
oriented away from zero. -/
private def splitCycleAnchorIndex {n : ℕ} [NeZero n] (k i : Fin n) : Fin n :=
  if i = 0 then 0 else if i.val ≤ k.val then i - 1 else i

/-- Original cycle edges used as anchors for the split transition system. -/
private def splitCycleAnchor (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k i : Fin c.length) : c.AugmentedTrailEdge cover q :=
  c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i)

/-- The split cycle anchor at each cycle position is incident with that vertex. -/
private theorem splitCycleAnchor_inc (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k i : Fin c.length) :
    (c.augmentedTrailMultigraph cover q).Inc (c.getVert i)
      (c.splitCycleAnchor cover q k i) := by
  change c.getVert i ∈
    (c.augmentedTrailMultigraph cover q).ends
      (c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i))
  rw [c.augmentedTrailMultigraph_ends_original]
  rw [Sym2.mem_iff]
  by_cases hi : i = 0
  · simp [splitCycleAnchorIndex, hi]
  · by_cases hik : i.val ≤ k.val
    · right
      simp only [splitCycleAnchorIndex, hi, hik, ↓reduceIte]
      rw [Fin.val_sub_one_of_ne_zero hi]
      congr 1
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · left
      simp [splitCycleAnchorIndex, hi, hik]

/-- Every original cycle edge except the distinguished split edge anchors an endpoint away
from the root. -/
private theorem exists_splitCycleAnchor_eq_original (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k j : Fin c.length) (hj : j ≠ k) :
    ∃ i : Fin c.length,
      i ≠ 0 ∧
      (c.augmentedTrailMultigraph cover q).Inc (c.getVert i)
        (c.augmentedOriginalEdge cover q j) ∧
      c.splitCycleAnchor cover q k i = c.augmentedOriginalEdge cover q j := by
  by_cases hlt : j.val < k.val
  · have hbound : j.val + 1 < c.length := lt_of_le_of_lt hlt k.isLt
    let i : Fin c.length := ⟨j.val + 1, hbound⟩
    have hi0 : i ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp [i] at hval
    have hik : i.val ≤ k.val := by simp [i]; omega
    have hindex : splitCycleAnchorIndex k i = j := by
      apply Fin.ext
      rw [splitCycleAnchorIndex, ite_eq_right hi0, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi0]
      simp [i]
    refine ⟨i, hi0, ?_, ?_⟩
    · change c.getVert i ∈
        (c.augmentedTrailMultigraph cover q).ends
          (c.augmentedOriginalEdge cover q j)
      rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      right
      simp [i]
    · simp only [splitCycleAnchor]
      rw [hindex]
  · have hgt : k.val < j.val := by
      have hneval : j.val ≠ k.val := fun h ↦ hj (Fin.ext h)
      omega
    have hj0 : j ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero] at hval
      omega
    have hindex : splitCycleAnchorIndex k j = j := by
      simp [splitCycleAnchorIndex, hj0, show ¬j.val ≤ k.val by omega]
    refine ⟨j, hj0, ?_, ?_⟩
    · change c.getVert j ∈
        (c.augmentedTrailMultigraph cover q).ends
          (c.augmentedOriginalEdge cover q j)
      rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      exact Or.inl rfl
    · simp only [splitCycleAnchor]
      rw [hindex]

/-- A split anchor never selects the distinguished edge when that edge carries a copy. -/
private theorem splitCycleAnchorIndex_ne_cut {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (i : Fin n) : splitCycleAnchorIndex cut.1 i ≠ cut.1 := by
  have hcut0 := cut.ne_zero q
  by_cases hi : i = 0
  · simpa [splitCycleAnchorIndex, hi] using hcut0.symm
  · by_cases hik : i.val ≤ cut.1.val
    · intro h
      have hval := congrArg Fin.val h
      rw [splitCycleAnchorIndex, ite_eq_right hi, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi] at hval
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · intro h
      have hval := congrArg Fin.val h
      simp [splitCycleAnchorIndex, hi, hik] at hval
      omega

/-- Split anchors in a multigraph with the distinguished parallel pair deleted. -/
private noncomputable def cutSplitCycleAnchor (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : Fin c.length) :
    c.CutAugmentedTrailEdge cover q cut :=
  c.cutOriginalEdge cover q cut (splitCycleAnchorIndex cut.1 i)
    (splitCycleAnchorIndex_ne_cut q cut i)

/-- Every cut split anchor is incident with its cycle vertex. -/
private theorem cutSplitCycleAnchor_inc (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : Fin c.length) :
    (c.cutAugmentedTrailMultigraph cover q cut).Inc (c.getVert i)
      (c.cutSplitCycleAnchor cover q cut i) := by
  change c.getVert i ∈
    (c.cutAugmentedTrailMultigraph cover q cut).ends
      (c.cutOriginalEdge cover q cut (splitCycleAnchorIndex cut.1 i) _)
  rw [c.cutAugmentedTrailMultigraph_ends_original, Sym2.mem_iff]
  by_cases hi : i = 0
  · simp [splitCycleAnchorIndex, hi]
  · by_cases hik : i.val ≤ cut.1.val
    · right
      simp only [splitCycleAnchorIndex, hi, hik, ↓reduceIte]
      rw [Fin.val_sub_one_of_ne_zero hi]
      congr 1
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · left
      simp [splitCycleAnchorIndex, hi, hik]

/-- Every retained original cycle edge is anchored at its endpoint away from the split. -/
private theorem exists_cutSplitCycleAnchor_eq_original (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (j : Fin c.length) (hj : j ≠ cut.1) :
    ∃ i : Fin c.length,
      i ≠ 0 ∧
      (c.cutAugmentedTrailMultigraph cover q cut).Inc (c.getVert i)
        (c.cutOriginalEdge cover q cut j hj) ∧
      c.cutSplitCycleAnchor cover q cut i =
        c.cutOriginalEdge cover q cut j hj := by
  by_cases hlt : j.val < cut.1.val
  · have hbound : j.val + 1 < c.length := lt_of_le_of_lt hlt cut.1.isLt
    let i : Fin c.length := ⟨j.val + 1, hbound⟩
    have hi0 : i ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp [i] at hval
    have hik : i.val ≤ cut.1.val := by simp [i]; omega
    have hindex : splitCycleAnchorIndex cut.1 i = j := by
      apply Fin.ext
      rw [splitCycleAnchorIndex, ite_eq_right hi0, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi0]
      simp [i]
    refine ⟨i, hi0, ?_, ?_⟩
    · change c.getVert i ∈
        (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutOriginalEdge cover q cut j hj)
      rw [c.cutAugmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      right
      simp [i]
    · apply Subtype.ext
      simp only [cutSplitCycleAnchor, cutOriginalEdge]
      rw [hindex]
  · have hgt : cut.1.val < j.val := by
      have hneval : j.val ≠ cut.1.val := fun h ↦ hj (Fin.ext h)
      omega
    have hj0 : j ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero] at hval
      omega
    have hindex : splitCycleAnchorIndex cut.1 j = j := by
      simp [splitCycleAnchorIndex, hj0, show ¬j.val ≤ cut.1.val by omega]
    refine ⟨j, hj0, ?_, ?_⟩
    · change c.getVert j ∈
        (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutOriginalEdge cover q cut j hj)
      rw [c.cutAugmentedTrailMultigraph_ends_original, Sym2.mem_iff]
      exact Or.inl rfl
    · apply Subtype.ext
      simp only [cutSplitCycleAnchor, cutOriginalEdge]
      rw [hindex]

/-- Every edge surviving a parallel-pair deletion is an original cycle edge, a cover edge,
or an uncut copied cycle edge. -/
private theorem cutAugmentedTrailEdge_cases (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (e : c.CutAugmentedTrailEdge cover q cut) :
    (∃ (j : Fin c.length) (hj : j ≠ cut.1),
      e = c.cutOriginalEdge cover q cut j hj) ∨
    (∃ (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge),
      e = c.cutCoverEdge cover q cut D f) ∨
    ∃ i : UncutActiveCycleCopy q cut,
      e = c.cutCopiedEdge cover q cut i := by
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
      cases e with
      | inl j =>
          have hj : j.down ≠ cut.1 := by
            intro h
            apply he
            rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
            left
            apply congrArg Sum.inl
            apply congrArg Sum.inl
            exact ULift.ext h
          left
          exact ⟨j.down, hj, by rfl⟩
      | inr f =>
          right
          left
          exact ⟨f.1, f.2, by rfl⟩
  | inr f =>
      rcases f with ⟨j, r⟩
      have hcopy : q.copies j = 1 := by
        have hpos : 0 < q.copies j := Nat.pos_of_ne_zero (by
          intro hzero
          simpa [hzero] using r.isLt)
        have hlt := q.copies_lt_two j
        omega
      let active : ActiveCycleCopy q := ⟨j, hcopy⟩
      have hne : active.1 ≠ cut.1 := by
        intro h
        have hj : j = cut.1 := h
        subst j
        apply he
        rw [(c.cycleParallelPair cover q cut.2).mem_range_edge_iff]
        right
        apply congrArg Sum.inr
        congr 1
        apply Fin.ext
        omega
      right
      right
      let i : UncutActiveCycleCopy q cut := ⟨active, hne⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inr
      dsimp only [i, active]
      congr 1
      apply Fin.ext
      omega

/-- A copied cycle edge away from the closing index is not incident with the cycle root. -/
private theorem augmentedCopiedEdge_not_inc_getVert_zero (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (i : ActiveCycleCopy q) (hlast : i.1 ≠ cycleLastIndex c.length) :
    ¬(c.augmentedTrailMultigraph cover q).Inc (c.getVert 0)
      (c.augmentedCopiedEdge cover q i.2) := by
  intro hinc
  change c.getVert 0 ∈
    s(c.getVert i.1, c.getVert (i.1.val + 1)) at hinc
  rw [hc.getVert_succ_eq_add_one] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · have hi0 : (0 : Fin c.length) = i.1 := hc.getVert_injective_fin h
    exact i.ne_zero q hi0.symm
  · have hadd : i.1 + 1 = 0 := hc.getVert_injective_fin h.symm
    have hsub : i.1 = (0 : Fin c.length) - 1 := eq_sub_iff_add_eq.mpr hadd
    have hone : (0 : Fin c.length) - 1 = cycleLastIndex c.length := by
      apply Fin.ext
      rw [sub_eq_add_neg, zero_add, Fin.val_neg]
      have htwo : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
      have hne : (1 : Fin c.length) ≠ 0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [Nat.mod_eq_of_lt htwo] at hval
      simp [hne, cycleLastIndex, Nat.mod_eq_of_lt htwo]
    exact hlast (hsub.trans hone)

/-- A retained copied cycle edge away from the closing index is not incident with the root
of the cycle. -/
private theorem cutCopiedEdge_not_inc_getVert_zero (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q) (i : UncutActiveCycleCopy q cut)
    (hlast : i.1.1 ≠ cycleLastIndex c.length) :
    ¬(c.cutAugmentedTrailMultigraph cover q cut).Inc (c.getVert 0)
      (c.cutCopiedEdge cover q cut i) := by
  intro hinc
  change c.getVert 0 ∈
    s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) at hinc
  rw [hc.getVert_succ_eq_add_one] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · have hi0 : (0 : Fin c.length) = i.1.1 := hc.getVert_injective_fin h
    exact i.1.ne_zero q hi0.symm
  · have hadd : i.1.1 + 1 = 0 := hc.getVert_injective_fin h.symm
    have hsub : i.1.1 = (0 : Fin c.length) - 1 :=
      eq_sub_iff_add_eq.mpr hadd
    have hone : (0 : Fin c.length) - 1 = cycleLastIndex c.length := by
      apply Fin.ext
      rw [sub_eq_add_neg, zero_add, Fin.val_neg]
      have htwo : 1 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
      have hne : (1 : Fin c.length) ≠ 0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [Nat.mod_eq_of_lt htwo] at hval
      simp [hne, cycleLastIndex, Nat.mod_eq_of_lt htwo]
    exact hlast (hsub.trans hone)

/-- In the closing-edge-cut preparation, the left transition edge is the split anchor at
the transition center. -/
private theorem forwardLastCutCycleTransition_left_eq_anchor [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 1)
    (i : UncutActiveCycleCopy (c.cycleEulerizationCompletion hc cover)
      (lastActiveCycleCopy (c.cycleEulerizationCompletion hc cover) hlast)) :
    let q := c.cycleEulerizationCompletion hc cover
    let cut := lastActiveCycleCopy q hlast
    c.cutSplitCycleAnchor cover q cut i.1.1 =
      (c.forwardLastCutCycleTransition hc cover q hlast i).left := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  have hi0 := i.1.ne_zero q
  have hle : i.1.1.val ≤ cut.1.val := by
    change i.1.1.val ≤ c.length - 1
    omega
  have hindex : splitCycleAnchorIndex cut.1 i.1.1 = i.1.1 - 1 := by
    simp [splitCycleAnchorIndex, hi0, hle]
  apply Subtype.ext
  change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex cut.1 i.1.1) =
    c.augmentedOriginalEdge cover q (i.1.1 - 1)
  rw [hindex]

/-- In the uncut split preparation, every copied-edge transition is anchored at its center
by its left edge when the distinguished edge has no copy. -/
private theorem exists_splitCycleTransition_center_anchor (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0)
    (hk : q.copies k = 0) (i : ActiveCycleCopy q) :
    let transition := c.splitCycleTransition hc cover q k hlast
    ∃ a : Fin c.length, (transition i).center = c.getVert a ∧
      c.splitCycleAnchor cover q k a = (transition i).left := by
  dsimp only
  by_cases hlt : i.1.val < k.val
  · refine ⟨i.1, ?_, ?_⟩
    · exact c.splitCycleTransition_center_of_lt hc cover q k hlast i hlt
    · have hi0 := i.ne_zero q
      have hindex : splitCycleAnchorIndex k i.1 = i.1 - 1 := by
        simp [splitCycleAnchorIndex, hi0, show i.1.val ≤ k.val by omega]
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k i.1) =
        (c.splitCycleTransition hc cover q k hlast i).left
      rw [c.splitCycleTransition_left, splitPartnerIndex,
        ite_eq_left hlt, hindex]
  · have hgt : k.val < i.1.val := by
      have hneval : i.1.val ≠ k.val := fun h ↦
        i.ne_of_copies_eq_zero q k hk (Fin.ext h)
      omega
    have hbound : i.1.val + 1 < c.length := i.val_add_one_lt q hlast
    let a : Fin c.length := ⟨i.1.val + 1, hbound⟩
    refine ⟨a, ?_, ?_⟩
    · exact c.splitCycleTransition_center_of_not_lt hc cover q k hlast i hlt
    · have ha0 : a ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [a] at hval
      have haK : ¬a.val ≤ k.val := by
        change ¬ i.1.val + 1 ≤ k.val
        omega
      have htwo : 1 < c.length := by omega
      have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt htwo
      have hadd : i.1.val + (1 : Fin c.length).val < c.length := by
        simpa only [hone] using hbound
      have hindex : splitCycleAnchorIndex k a = i.1 + 1 := by
        apply Fin.ext
        rw [Fin.val_add_eq_of_add_lt hadd, hone]
        simp [splitCycleAnchorIndex, ha0, haK, a]
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex k a) =
        (c.splitCycleTransition hc cover q k hlast i).left
      rw [c.splitCycleTransition_left, splitPartnerIndex,
        ite_eq_right hlt, hindex]

/-- In the distinguished-edge-cut preparation, every retained transition is anchored at its
center by its left edge. -/
private theorem exists_cutSplitCycleTransition_center_anchor [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (cut : ActiveCycleCopy (c.cycleEulerizationCompletion hc cover))
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 0)
    (i : UncutActiveCycleCopy (c.cycleEulerizationCompletion hc cover) cut) :
    let q := c.cycleEulerizationCompletion hc cover
    let transition := c.cutSplitCycleTransition hc cover q cut hlast
    ∃ a : Fin c.length, (transition i).center = c.getVert a ∧
      c.cutSplitCycleAnchor cover q cut a = (transition i).left := by
  classical
  dsimp only
  let q := c.cycleEulerizationCompletion hc cover
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  by_cases hlt : i.1.1.val < cut.1.val
  · refine ⟨i.1.1, ?_, ?_⟩
    · rw [c.cutSplitCycleTransition_center,
        c.splitCycleTransition_center_of_lt hc cover q cut.1 hlast i.1 hlt]
    · have hi0 := i.1.ne_zero q
      have hindex : splitCycleAnchorIndex cut.1 i.1.1 = i.1.1 - 1 := by
        simp [splitCycleAnchorIndex, hi0, show i.1.1.val ≤ cut.1.val by omega]
      apply Subtype.ext
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex cut.1 i.1.1) =
        (c.splitCycleTransition hc cover q cut.1 hlast i.1).left
      rw [c.splitCycleTransition_left, splitPartnerIndex, ite_eq_left hlt, hindex]
  · have hgt : cut.1.val < i.1.1.val := by
      have hneval : i.1.1.val ≠ cut.1.val := fun h ↦ i.2 (Fin.ext h)
      omega
    have hbound : i.1.1.val + 1 < c.length := i.1.val_add_one_lt q hlast
    let a : Fin c.length := ⟨i.1.1.val + 1, hbound⟩
    refine ⟨a, ?_, ?_⟩
    · rw [c.cutSplitCycleTransition_center,
        c.splitCycleTransition_center_of_not_lt hc cover q cut.1 hlast i.1 hlt]
    · have ha0 : a ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [a] at hval
      have haCut : ¬a.val ≤ cut.1.val := by
        change ¬ i.1.1.val + 1 ≤ cut.1.val
        omega
      have htwo : 1 < c.length := by omega
      have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt htwo
      have hadd : i.1.1.val + (1 : Fin c.length).val < c.length := by
        simpa only [hone] using hbound
      have hindex : splitCycleAnchorIndex cut.1 a = i.1.1 + 1 := by
        apply Fin.ext
        rw [Fin.val_add_eq_of_add_lt hadd, hone]
        simp [splitCycleAnchorIndex, ha0, haCut, a]
      apply Subtype.ext
      change c.augmentedOriginalEdge cover q (splitCycleAnchorIndex cut.1 a) =
        (c.splitCycleTransition hc cover q cut.1 hlast i.1).left
      rw [c.splitCycleTransition_left, splitPartnerIndex, ite_eq_right hlt, hindex]

/-- At an edge incident with the cycle root, the other endpoint is either anchored by that
edge or is an off-cycle degree-two vertex. -/
private theorem cutRootEdge_other_endpoint [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (cut : ActiveCycleCopy q)
    (anchor : V → c.CutAugmentedTrailEdge cover q cut)
    (hcycleAnchor : ∀ i : Fin c.length, anchor (c.getVert i) =
      c.cutSplitCycleAnchor cover q cut i)
    (hcopyLast : ∀ i : UncutActiveCycleCopy q cut,
      i.1.1 ≠ cycleLastIndex c.length)
    (e : c.CutAugmentedTrailEdge cover q cut)
    (hrootInc : (c.cutAugmentedTrailMultigraph cover q cut).Inc x e) :
    (∃ z, z ≠ x ∧
      (c.cutAugmentedTrailMultigraph cover q cut).Inc z e ∧ anchor z = e) ∨
    ∃ z, z ≠ x ∧
      (c.cutAugmentedTrailMultigraph cover q cut).Inc z e ∧
      (c.cutAugmentedTrailMultigraph cover q cut).degree z = 2 := by
  rcases c.cutAugmentedTrailEdge_cases cover q cut e with
    ⟨j, hj, rfl⟩ | ⟨D, f, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨a, ha0, hainc, haanchor⟩ :=
      c.exists_cutSplitCycleAnchor_eq_original cover q cut j hj
    left
    refine ⟨c.getVert a, ?_, hainc, ?_⟩
    · intro hax
      have ha : a = 0 := by
        apply hc.getVert_injective_fin
        exact hax.trans c.getVert_zero.symm
      exact ha0 ha
    · rw [hcycleAnchor a, haanchor]
  · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
    have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
    right
    refine ⟨z, ?_, ?_, c.cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q cut hzout⟩
    · intro hzx
      apply hzout
      subst z
      simpa only [c.getVert_zero] using c.getVert_mem_support 0
    · exact hzends
  · exfalso
    apply c.cutCopiedEdge_not_inc_getVert_zero hc cover q cut i (hcopyLast i)
    simpa only [c.getVert_zero] using hrootInc

/-- Every augmented edge is an original cycle edge, a component-cover edge, or an active
copied cycle edge. -/
private theorem augmentedTrailEdge_cases (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (e : c.AugmentedTrailEdge cover q) :
    (∃ j : Fin c.length, e = c.augmentedOriginalEdge cover q j) ∨
    (∃ (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge),
      e = c.augmentedCoverEdge cover q D f) ∨
    ∃ i : ActiveCycleCopy q, e = c.augmentedCopiedEdge cover q i.2 := by
  cases e with
  | inl e =>
      cases e with
      | inl j => exact Or.inl ⟨j.down, rfl⟩
      | inr f => exact Or.inr (Or.inl ⟨f.1, f.2, rfl⟩)
  | inr f =>
      rcases f with ⟨j, r⟩
      have hcopy : q.copies j = 1 := by
        have hpos : 0 < q.copies j := Nat.pos_of_ne_zero (by
          intro hzero
          simpa [hzero] using r.isLt)
        have hlt := q.copies_lt_two j
        omega
      let i : ActiveCycleCopy q := ⟨j, hcopy⟩
      right
      right
      refine ⟨i, ?_⟩
      apply congrArg Sum.inr
      dsimp only [i]
      congr 1
      apply Fin.ext
      omega

/-- At a root-incident edge in the uncut split preparation, the other endpoint is either
anchored or has degree two. -/
private theorem splitRootEdge_other_endpoint [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hk0 : k ≠ 0)
    (anchor : V → c.AugmentedTrailEdge cover q)
    (hcycleAnchor : ∀ i : Fin c.length, anchor (c.getVert i) =
      c.splitCycleAnchor cover q k i)
    (hdegreeK : (c.augmentedTrailMultigraph cover q).degree (c.getVert k) = 2)
    (hcopyLast : ∀ i : ActiveCycleCopy q,
      i.1 ≠ cycleLastIndex c.length)
    (e : c.AugmentedTrailEdge cover q)
    (hrootInc : (c.augmentedTrailMultigraph cover q).Inc x e) :
    (∃ z, z ≠ x ∧
      (c.augmentedTrailMultigraph cover q).Inc z e ∧ anchor z = e) ∨
    ∃ z, z ≠ x ∧
      (c.augmentedTrailMultigraph cover q).Inc z e ∧
      (c.augmentedTrailMultigraph cover q).degree z = 2 := by
  rcases c.augmentedTrailEdge_cases cover q e with
    ⟨j, rfl⟩ | ⟨D, f, rfl⟩ | ⟨i, rfl⟩
  · by_cases hj : j = k
    · subst j
      right
      refine ⟨c.getVert k, ?_, ?_, hdegreeK⟩
      · intro hyx
        have hk : k = 0 := by
          apply hc.getVert_injective_fin
          exact hyx.trans c.getVert_zero.symm
        exact hk0 hk
      · change c.getVert k ∈
          (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q k)
        rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
        exact Or.inl rfl
    · obtain ⟨a, ha0, hainc, haanchor⟩ :=
        c.exists_splitCycleAnchor_eq_original cover q k j hj
      left
      refine ⟨c.getVert a, ?_, hainc, ?_⟩
      · intro hax
        have ha : a = 0 := by
          apply hc.getVert_injective_fin
          exact hax.trans c.getVert_zero.symm
        exact ha0 ha
      · rw [hcycleAnchor a, haanchor]
  · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
    have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
    right
    refine ⟨z, ?_, ?_, c.augmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q hzout⟩
    · intro hzx
      apply hzout
      subst z
      simpa only [c.getVert_zero] using c.getVert_mem_support 0
    · exact hzends
  · exfalso
    apply c.augmentedCopiedEdge_not_inc_getVert_zero hc cover q i (hcopyLast i)
    simpa only [c.getVert_zero] using hrootInc

end Walk

namespace EdgeIndexedMultigraph

namespace IndexedWalk

variable {V E : Type*} (M : EdgeIndexedMultigraph V E)

/-- Adjacent expanded edge identities determine the corresponding pass of the cyclic
Euler-circuit encoding. -/
private theorem toCyclicCircuit_exists_pass_of_edgesAdjacent [Nonempty E]
    {u : V} (p : M.IndexedWalk u u) (hp : p.IsEulerian)
    (e f : E) (h : EdgesAdjacent e f p.edges) :
    let C := p.toCyclicCircuit M hp
    ∃ i, (C.incoming M i = e ∧ C.edge i = f) ∨
      (C.incoming M i = f ∧ C.edge i = e) := by
  classical
  let C := p.toCyclicCircuit M hp
  rcases h with ⟨before, after, h | h⟩
  · have hlt : before.length + 1 < C.size := by
      change before.length + 1 < p.edges.length
      rw [h]
      simp
    let i : Fin C.size := ⟨before.length + 1, hlt⟩
    have hi : i.val ≠ 0 := by simp [i]
    have hincoming : C.incoming M i = e := by
      rw [CyclicCircuit.incoming, show cyclicPrev C.size C.size_pos i =
        ⟨before.length, by omega⟩ by
          apply Fin.ext
          rw [cyclicPrev_val_of_ne_zero C.size C.size_pos i hi]
          simp [i]]
      have hbound : before.length < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length, hbound⟩ = e
      have hget : p.edges[before.length]? = some e := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    have houtgoing : C.edge i = f := by
      have hbound : before.length + 1 < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length + 1, hbound⟩ = f
      have hget : p.edges[before.length + 1]? = some f := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    exact ⟨i, Or.inl ⟨hincoming, houtgoing⟩⟩
  · have hlt : before.length + 1 < C.size := by
      change before.length + 1 < p.edges.length
      rw [h]
      simp
    let i : Fin C.size := ⟨before.length + 1, hlt⟩
    have hi : i.val ≠ 0 := by simp [i]
    have hincoming : C.incoming M i = f := by
      rw [CyclicCircuit.incoming, show cyclicPrev C.size C.size_pos i =
        ⟨before.length, by omega⟩ by
          apply Fin.ext
          rw [cyclicPrev_val_of_ne_zero C.size C.size_pos i hi]
          simp [i]]
      have hbound : before.length < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length, hbound⟩ = f
      have hget : p.edges[before.length]? = some f := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    have houtgoing : C.edge i = e := by
      have hbound : before.length + 1 < p.edges.length := by rw [h]; simp
      change p.edges.get ⟨before.length + 1, hbound⟩ = e
      have hget : p.edges[before.length + 1]? = some e := by rw [h]; simp
      obtain ⟨_, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
      simpa using hvalue
    exact ⟨i, Or.inr ⟨hincoming, houtgoing⟩⟩

end IndexedWalk

namespace CyclicCircuit

universe u v

variable {V : Type u} {E : Type v} (M : EdgeIndexedMultigraph V E)
variable (C : M.CyclicCircuit)

/-- The only common endpoint of the two edges in a transition is its center. -/
private theorem transition_eq_center_of_inc_left_right
    (t : M.EdgeTransition) (z : V)
    (hleft : M.Inc z t.left) (hright : M.Inc z t.right) : z = t.center := by
  rw [EdgeIndexedMultigraph.Inc, t.left_ends] at hleft
  rw [EdgeIndexedMultigraph.Inc, t.right_ends] at hright
  rcases Sym2.mem_iff.mp hleft with hleft | hleft <;>
    rcases Sym2.mem_iff.mp hright with hright | hright
  · have hsame : t.before = t.center := hleft.symm.trans hright
    exact False.elim (M.loopless t.left t.center (by simpa [hsame] using t.left_ends))
  · exact False.elim (t.before_ne_after (hleft.symm.trans hright))
  · exact hleft
  · have hsame : t.center = t.after := hleft.symm.trans hright
    exact False.elim (M.loopless t.right t.center (by simpa [hsame] using t.right_ends))

/-- If a transition's left edge is the anchor at its center, its right edge has an
unmarked circuit endpoint. -/
private theorem transitionRight_has_unmarked_endpoint
    (anchor : V → E) (t : M.EdgeTransition)
    (hanchor : anchor t.center = t.left)
    (hpass : ∃ j, (C.incoming M j = t.left ∧ C.edge j = t.right) ∨
      (C.incoming M j = t.right ∧ C.edge j = t.left))
    (i : Fin C.size) (hi : C.edge i = t.right) :
    C.anchorMarked M anchor i = false ∨
      C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false := by
  classical
  obtain ⟨j, hpass | hpass⟩ := hpass
  · have hjvertex : C.vertex j = t.center := by
      apply transition_eq_center_of_inc_left_right M t
      · rw [← hpass.1]
        simp [EdgeIndexedMultigraph.Inc]
      · rw [← hpass.2]
        rw [EdgeIndexedMultigraph.Inc, C.ends_edge]
        simp
    have hkeeps : C.Keeps M anchor j := by
      left
      exact hpass.1.trans ((congrArg anchor hjvertex).trans hanchor).symm
    have hfalse : C.anchorMarked M anchor j = false := by
      simp [CyclicCircuit.anchorMarked, hkeeps]
    left
    have hij : i = j := C.edge_bijective.1 (hi.trans hpass.2.symm)
    simpa [hij] using hfalse
  · have hjvertex : C.vertex j = t.center := by
      apply transition_eq_center_of_inc_left_right M t
      · rw [← hpass.2]
        rw [EdgeIndexedMultigraph.Inc, C.ends_edge]
        simp
      · rw [← hpass.1]
        simp [EdgeIndexedMultigraph.Inc]
    have hkeeps : C.Keeps M anchor j := by
      right
      exact hpass.2.trans ((congrArg anchor hjvertex).trans hanchor).symm
    have hfalse : C.anchorMarked M anchor j = false := by
      simp [CyclicCircuit.anchorMarked, hkeeps]
    right
    have hiprev : i = cyclicPrev C.size C.size_pos j := by
      apply C.edge_bijective.1
      exact hi.trans hpass.1.symm
    rw [hiprev, cyclicNext_prev]
    exact hfalse

/-- An edge used as an anchor at one endpoint has an unmarked circuit endpoint. -/
private theorem anchorEdge_has_unmarked_endpoint
    (anchor : V → E) (i : Fin C.size) (z : V)
    (hinc : M.Inc z (C.edge i)) (hanchor : anchor z = C.edge i) :
    C.anchorMarked M anchor i = false ∨
      C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false := by
  classical
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · left
    have hkeeps : C.Keeps M anchor i := by
      right
      exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]
  · right
    have hkeeps : C.Keeps M anchor
        (cyclicNext C.size C.size_pos i) := by
      left
      rw [CyclicCircuit.incoming, cyclicPrev_next]
      exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]

/-- An edge incident with a degree-two vertex has an unmarked circuit endpoint. -/
private theorem degreeTwo_has_unmarked_endpoint
    (anchor : V → E) (hanchorInc : ∀ z, M.Inc z (anchor z))
    (i : Fin C.size) (z : V) (hinc : M.Inc z (C.edge i))
    (hdegree : M.degree z = 2) :
    C.anchorMarked M anchor i = false ∨
      C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false := by
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · left
    apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree
  · right
    apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree

/-- An anchored non-root endpoint of the outgoing root edge is unmarked. -/
private theorem anchorEdge_next_unmarked
    (anchor : V → E) (start : Fin C.size) (root z : V)
    (hroot : C.vertex start = root) (hz : z ≠ root)
    (hinc : M.Inc z (C.edge start)) (hanchor : anchor z = C.edge start) :
    C.anchorMarked M anchor (cyclicNext C.size C.size_pos start) = false := by
  classical
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · exact False.elim (hz (h.trans hroot))
  · have hkeeps : C.Keeps M anchor
        (cyclicNext C.size C.size_pos start) := by
      left
      rw [CyclicCircuit.incoming, cyclicPrev_next]
      exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]

/-- A degree-two non-root endpoint of the outgoing root edge is unmarked. -/
private theorem degreeTwo_next_unmarked
    (anchor : V → E) (hanchorInc : ∀ z, M.Inc z (anchor z))
    (start : Fin C.size) (root z : V) (hroot : C.vertex start = root)
    (hz : z ≠ root) (hinc : M.Inc z (C.edge start))
    (hdegree : M.degree z = 2) :
    C.anchorMarked M anchor (cyclicNext C.size C.size_pos start) = false := by
  rw [EdgeIndexedMultigraph.Inc, C.ends_edge] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · exact False.elim (hz (h.trans hroot))
  · apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree

/-- An anchored non-root endpoint of the incoming root edge is unmarked. -/
private theorem anchorEdge_prev_unmarked
    (anchor : V → E) (start : Fin C.size) (root z : V)
    (hroot : C.vertex start = root) (hz : z ≠ root)
    (hinc : M.Inc z (C.incoming M start))
    (hanchor : anchor z = C.incoming M start) :
    C.anchorMarked M anchor (cyclicPrev C.size C.size_pos start) = false := by
  classical
  rw [EdgeIndexedMultigraph.Inc, C.ends_incoming] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · have hkeeps : C.Keeps M anchor
        (cyclicPrev C.size C.size_pos start) := by
      right
      exact hanchor.symm.trans (congrArg anchor h)
    simp [CyclicCircuit.anchorMarked, hkeeps]
  · exact False.elim (hz (h.trans hroot))

/-- A degree-two non-root endpoint of the incoming root edge is unmarked. -/
private theorem degreeTwo_prev_unmarked
    (anchor : V → E) (hanchorInc : ∀ z, M.Inc z (anchor z))
    (start : Fin C.size) (root z : V) (hroot : C.vertex start = root)
    (hz : z ≠ root) (hinc : M.Inc z (C.incoming M start))
    (hdegree : M.degree z = 2) :
    C.anchorMarked M anchor (cyclicPrev C.size C.size_pos start) = false := by
  rw [EdgeIndexedMultigraph.Inc, C.ends_incoming] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · apply C.anchorMarked_eq_false_of_degree_eq_two M anchor hanchorInc
    simpa [h] using hdegree
  · exact False.elim (hz (h.trans hroot))

/-- An anchor marking satisfying the local endpoint conditions shortcuts to a rooted
Hamiltonian cycle in the graph square. -/
private theorem anchorMarked_toHasStrongSquareCycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (support : Set V) (anchor : V → E)
    (hinc : ∀ z, M.Inc z (anchor z))
    (hdegree : ∀ z ∉ support, M.degree z = 2)
    (hsquare : ∀ e, M.ends e ∈ G.square.edgeSet)
    (horiginal : ∀ e a b, M.ends e = s(a, b) →
      (a ∈ support ∨ b ∈ support) → G.Adj a b)
    (start : Fin C.size) (hroot : C.vertex start = root)
    (hstart : C.anchorMarked M anchor start = false)
    (hedge : ∀ i, C.anchorMarked M anchor i = false ∨
      C.anchorMarked M anchor (cyclicNext C.size C.size_pos i) = false)
    (hnext : C.anchorMarked M anchor
      (cyclicNext C.size C.size_pos start) = false)
    (hprev : C.anchorMarked M anchor
      (cyclicPrev C.size C.size_pos start) = false)
    (hrootSupport : root ∈ support) (hcard : 3 ≤ Fintype.card V) :
    G.HasStrongSquareCycle root := by
  classical
  let marked := C.anchorMarked M anchor
  have hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false :=
    C.existsUnique_anchorMarked M anchor hinc
  have hsquare' (i : Fin C.size) : G.square.Adj (C.vertex i)
      (C.vertex (cyclicNext C.size C.size_pos i)) := by
    apply G.square.mem_edgeSet.mp
    rw [← C.ends_edge]
    exact hsquare (C.edge i)
  have horiginal' (i : Fin C.size)
      (hi : marked i = true ∨
        marked (cyclicNext C.size C.size_pos i) = true) :
      G.Adj (C.vertex i)
        (C.vertex (cyclicNext C.size C.size_pos i)) := by
    apply horiginal (C.edge i) _ _ (C.ends_edge i)
    rcases hi with hi | hi
    · left
      by_contra houtside
      have hfalse := C.anchorMarked_eq_false_of_degree_eq_two M anchor hinc i
        (hdegree (C.vertex i) houtside)
      exact Bool.false_ne_true (hfalse.symm.trans hi)
    · right
      let j := cyclicNext C.size C.size_pos i
      by_contra houtside
      have hfalse := C.anchorMarked_eq_false_of_degree_eq_two M anchor hinc j
        (hdegree (C.vertex j) houtside)
      exact Bool.false_ne_true (hfalse.symm.trans hi)
  have hnextAdj : G.Adj root
      (C.vertex (cyclicNext C.size C.size_pos start)) := by
    rw [← hroot]
    apply horiginal (C.edge start) _ _ (C.ends_edge start)
    exact Or.inl (hroot ▸ hrootSupport)
  have hprevAdj : G.Adj
      (C.vertex (cyclicPrev C.size C.size_pos start)) root := by
    rw [← hroot]
    let i := cyclicPrev C.size C.size_pos start
    apply horiginal (C.edge i) _ _
    · simpa [i] using C.ends_edge i
    · exact Or.inr (hroot ▸ hrootSupport)
  exact (SquareMarking.ofLocal M C G root start marked hroot hstart hunique
    hedge hsquare' horiginal' hnext hprev hnextAdj hprevAdj hcard).toHasStrongSquareCycle

end CyclicCircuit

end EdgeIndexedMultigraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

/-- The uncut two-arc prepared Euler circuit lifts to a rooted Hamiltonian cycle in the
square when the distinguished bound vertex has no outgoing copied edge. -/
private theorem hasStrongSquareCycle_of_split [Fintype V] [DecidableEq V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] (k : Fin c.length) (hk0 : k ≠ 0)
    (hbound : c.IsBoundVertex (c.getVert k))
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 0)
    (hk : (c.cycleEulerizationCompletion hc cover).copies k = 0)
    (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.augmentedTrailMultigraph cover q
  let transition := c.splitCycleTransition hc cover q k hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.splitCycleTransition_edge_injective hc cover q k hlast
  obtain ⟨u, p, hp⟩ := c.exists_split_compressed_eulerian hc cover k hlast
  let tour := M.expandTransitions transition p
  have htour : tour.IsEulerian :=
    M.expandTransitions_isEulerian transition hinj p hp
  let edge0 := c.augmentedOriginalEdge cover q 0
  let _ : Nonempty (c.AugmentedTrailEdge cover q) := ⟨edge0⟩
  let C := tour.toCyclicCircuit M htour
  let cycleAnchor := c.splitCycleAnchor cover q k
  have hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i) :=
    c.splitCycleAnchor_inc cover q k
  have hdegree : ∀ z ∉ c.support, M.degree z = 2 := by
    intro z hz
    exact c.augmentedTrailMultigraph_degree_eq_two_of_not_mem hc cover q hz
  have hdegreeK : M.degree (c.getVert k) = 2 := by
    exact c.augmentedTrailMultigraph_degree_eq_two_of_bound hc cover k hbound hk
  obtain ⟨anchor, hanchorInc, hcycleAnchor⟩ :=
    hc.exists_incident_anchor M cycleAnchor hcycleInc hdegree
  obtain ⟨start, ⟨hstartVertex, hstart⟩, _⟩ :=
    C.existsUnique_anchorMarked M anchor hanchorInc x
  have hedge (pos : Fin C.size) :
      C.anchorMarked M anchor pos = false ∨
        C.anchorMarked M anchor
          (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos pos) = false := by
    rcases c.augmentedTrailEdge_cases cover q (C.edge pos) with
      ⟨j, he⟩ | ⟨D, f, he⟩ | ⟨i, he⟩
    · by_cases hj : j = k
      · subst j
        apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos
          (c.getVert k)
        · rw [he]
          change c.getVert k ∈
            M.ends (c.augmentedOriginalEdge cover q k)
          rw [c.augmentedTrailMultigraph_ends_original, Sym2.mem_iff]
          exact Or.inl rfl
        · exact hdegreeK
      · obtain ⟨a, _, hainc, haedge⟩ :=
          c.exists_splitCycleAnchor_eq_original cover q k j hj
        apply C.anchorEdge_has_unmarked_endpoint M anchor pos (c.getVert a)
        · simpa only [he] using hainc
        · rw [hcycleAnchor a]
          change c.splitCycleAnchor cover q k a = C.edge pos
          exact haedge.trans he.symm
    · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
      have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
      apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos z
      · rw [he]
        exact hzends
      · exact hdegree z hzout
    · have hadjacent := M.expandTransitions_edges_adjacent transition p i
        (hp.2 (Sum.inr i))
      have hpass := tour.toCyclicCircuit_exists_pass_of_edgesAdjacent M htour
        (transition i).left (transition i).right hadjacent
      obtain ⟨a, hcenter, hleft⟩ :=
        c.exists_splitCycleTransition_center_anchor hc cover q k hlast hk i
      apply C.transitionRight_has_unmarked_endpoint M anchor (transition i)
      · rw [hcenter, hcycleAnchor a]
        exact hleft
      · exact hpass
      · rw [c.splitCycleTransition_right]
        exact he
  have hcopyLast : ∀ i : ActiveCycleCopy q,
      i.1 ≠ cycleLastIndex c.length := by
    intro i
    exact i.ne_of_copies_eq_zero q _ hlast
  have hnext : C.anchorMarked M anchor
      (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.edge start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge, Sym2.mem_iff]
      exact Or.inl hstartVertex.symm
    rcases c.splitRootEdge_other_endpoint hc cover q k hk0 anchor hcycleAnchor
        hdegreeK hcopyLast (C.edge start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_next_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_next_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  have hprev : C.anchorMarked M anchor
      (EdgeIndexedMultigraph.cyclicPrev C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.incoming M start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_incoming, Sym2.mem_iff]
      exact Or.inr hstartVertex.symm
    rcases c.splitRootEdge_other_endpoint hc cover q k hk0 anchor hcycleAnchor
        hdegreeK hcopyLast (C.incoming M start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_prev_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_prev_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  apply C.anchorMarked_toHasStrongSquareCycle M G x {z | z ∈ c.support}
    anchor hanchorInc
    hdegree (c.augmentedTrailMultigraph_square_adj cover q)
    (c.augmentedTrailMultigraph_cycle_edge cover q) start
    hstartVertex hstart hedge hnext hprev
  · change x ∈ c.support
    simpa only [c.getVert_zero] using c.getVert_mem_support 0
  · exact hcard

/-- The prepared Euler circuit with its closing parallel pair deleted lifts to a rooted
Hamiltonian cycle in the square. -/
private theorem hasStrongSquareCycle_of_forwardLastCut [Fintype V] [DecidableEq V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 1)
    (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  let cut := lastActiveCycleCopy q hlast
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.forwardLastCutCycleTransition hc cover q hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.forwardLastCutCycleTransition_edge_injective hc cover q hlast
  obtain ⟨u, p, hp⟩ := c.exists_forwardLastCut_compressed_eulerian hc cover hlast
  let tour := M.expandTransitions transition p
  have htour : tour.IsEulerian :=
    M.expandTransitions_isEulerian transition hinj p hp
  have hzeroLast : (0 : Fin c.length) ≠ cut.1 := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = c.length - 1 at hval
    have hthree := hc.three_le_length
    omega
  let edge0 := c.cutOriginalEdge cover q cut 0 hzeroLast
  let _ : Nonempty (c.CutAugmentedTrailEdge cover q cut) := ⟨edge0⟩
  let C := tour.toCyclicCircuit M htour
  let cycleAnchor := c.cutSplitCycleAnchor cover q cut
  have hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i) :=
    c.cutSplitCycleAnchor_inc cover q cut
  have hdegree : ∀ z ∉ c.support, M.degree z = 2 := by
    intro z hz
    exact c.cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q cut hz
  obtain ⟨anchor, hanchorInc, hcycleAnchor⟩ :=
    hc.exists_incident_anchor M cycleAnchor hcycleInc hdegree
  obtain ⟨start, ⟨hstartVertex, hstart⟩, _⟩ :=
    C.existsUnique_anchorMarked M anchor hanchorInc x
  have hedge (pos : Fin C.size) :
      C.anchorMarked M anchor pos = false ∨
        C.anchorMarked M anchor
          (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos pos) = false := by
    rcases c.cutAugmentedTrailEdge_cases cover q cut (C.edge pos) with
      ⟨j, hj, he⟩ | ⟨D, f, he⟩ | ⟨i, he⟩
    · obtain ⟨a, _, hainc, haedge⟩ :=
        c.exists_cutSplitCycleAnchor_eq_original cover q cut j hj
      apply C.anchorEdge_has_unmarked_endpoint M anchor pos (c.getVert a)
      · simpa only [he] using hainc
      · rw [hcycleAnchor a]
        change c.cutSplitCycleAnchor cover q cut a = C.edge pos
        exact haedge.trans he.symm
    · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
      have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
      apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos z
      · rw [he]
        exact hzends
      · exact hdegree z hzout
    · have hadjacent := M.expandTransitions_edges_adjacent transition p i
        (hp.2 (Sum.inr i))
      have hpass := tour.toCyclicCircuit_exists_pass_of_edgesAdjacent M htour
        (transition i).left (transition i).right hadjacent
      apply C.transitionRight_has_unmarked_endpoint M anchor (transition i)
      · rw [c.forwardLastCutCycleTransition_center,
          hcycleAnchor i.1.1]
        exact c.forwardLastCutCycleTransition_left_eq_anchor hc cover hlast i
      · exact hpass
      · rw [c.forwardLastCutCycleTransition_right]
        exact he
  have hcopyLast : ∀ i : UncutActiveCycleCopy q cut,
      i.1.1 ≠ cycleLastIndex c.length := by
    intro i
    simpa only [cut, lastActiveCycleCopy] using i.2
  have hnext : C.anchorMarked M anchor
      (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.edge start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge, Sym2.mem_iff]
      exact Or.inl hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
        hcopyLast (C.edge start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_next_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_next_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  have hprev : C.anchorMarked M anchor
      (EdgeIndexedMultigraph.cyclicPrev C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.incoming M start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_incoming, Sym2.mem_iff]
      exact Or.inr hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
        hcopyLast (C.incoming M start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_prev_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_prev_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  apply C.anchorMarked_toHasStrongSquareCycle M G x {z | z ∈ c.support}
    anchor hanchorInc
    hdegree (c.cutAugmentedTrailMultigraph_square_adj cover q cut)
    (c.cutAugmentedTrailMultigraph_cycle_edge cover q cut) start
    hstartVertex hstart hedge hnext hprev
  · change x ∈ c.support
    simpa only [c.getVert_zero] using c.getVert_mem_support 0
  · exact hcard

/-- The prepared Euler circuit with a distinguished parallel pair deleted lifts to a rooted
Hamiltonian cycle in the square. -/
private theorem hasStrongSquareCycle_of_cutSplit [Fintype V] [DecidableEq V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (cut : ActiveCycleCopy (c.cycleEulerizationCompletion hc cover))
    (hlast : (c.cycleEulerizationCompletion hc cover).copies
      (cycleLastIndex c.length) = 0)
    (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  classical
  let q := c.cycleEulerizationCompletion hc cover
  let M := c.cutAugmentedTrailMultigraph cover q cut
  let transition := c.cutSplitCycleTransition hc cover q cut hlast
  have hinj : Function.Injective (M.transitionEdge transition) :=
    c.cutSplitCycleTransition_edge_injective hc cover q cut hlast
  obtain ⟨u, p, hp⟩ := c.exists_cutSplit_compressed_eulerian hc cover cut hlast
  let tour := M.expandTransitions transition p
  have htour : tour.IsEulerian :=
    M.expandTransitions_isEulerian transition hinj p hp
  have hzeroCut : (0 : Fin c.length) ≠ cut.1 := (cut.ne_zero q).symm
  let edge0 := c.cutOriginalEdge cover q cut 0 hzeroCut
  let _ : Nonempty (c.CutAugmentedTrailEdge cover q cut) := ⟨edge0⟩
  let C := tour.toCyclicCircuit M htour
  let cycleAnchor := c.cutSplitCycleAnchor cover q cut
  have hcycleInc : ∀ i : Fin c.length, M.Inc (c.getVert i) (cycleAnchor i) :=
    c.cutSplitCycleAnchor_inc cover q cut
  have hdegree : ∀ z ∉ c.support, M.degree z = 2 := by
    intro z hz
    exact c.cutAugmentedTrailMultigraph_degree_eq_two_of_not_mem
      hc cover q cut hz
  obtain ⟨anchor, hanchorInc, hcycleAnchor⟩ :=
    hc.exists_incident_anchor M cycleAnchor hcycleInc hdegree
  obtain ⟨start, ⟨hstartVertex, hstart⟩, _⟩ :=
    C.existsUnique_anchorMarked M anchor hanchorInc x
  have hedge (pos : Fin C.size) :
      C.anchorMarked M anchor pos = false ∨
        C.anchorMarked M anchor
          (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos pos) = false := by
    rcases c.cutAugmentedTrailEdge_cases cover q cut (C.edge pos) with
      ⟨j, hj, he⟩ | ⟨D, f, he⟩ | ⟨i, he⟩
    · obtain ⟨a, _, hainc, haedge⟩ :=
        c.exists_cutSplitCycleAnchor_eq_original cover q cut j hj
      apply C.anchorEdge_has_unmarked_endpoint M anchor pos (c.getVert a)
      · simpa only [he] using hainc
      · rw [hcycleAnchor a]
        change c.cutSplitCycleAnchor cover q cut a = C.edge pos
        exact haedge.trans he.symm
    · obtain ⟨z, hzD, hzends⟩ := (cover D).meets_component f
      have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
      apply C.degreeTwo_has_unmarked_endpoint M anchor hanchorInc pos z
      · rw [he]
        exact hzends
      · exact hdegree z hzout
    · have hadjacent := M.expandTransitions_edges_adjacent transition p i
        (hp.2 (Sum.inr i))
      have hpass := tour.toCyclicCircuit_exists_pass_of_edgesAdjacent M htour
        (transition i).left (transition i).right hadjacent
      obtain ⟨a, hcenter, hleft⟩ :=
        c.exists_cutSplitCycleTransition_center_anchor hc cover cut hlast i
      apply C.transitionRight_has_unmarked_endpoint M anchor (transition i)
      · rw [hcenter, hcycleAnchor a]
        exact hleft
      · exact hpass
      · rw [c.cutSplitCycleTransition_right]
        exact he
  have hcopyLast : ∀ i : UncutActiveCycleCopy q cut,
      i.1.1 ≠ cycleLastIndex c.length := by
    intro i
    exact i.1.ne_of_copies_eq_zero q _ hlast
  have hnext : C.anchorMarked M anchor
      (EdgeIndexedMultigraph.cyclicNext C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.edge start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_edge, Sym2.mem_iff]
      exact Or.inl hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
        hcopyLast (C.edge start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_next_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_next_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  have hprev : C.anchorMarked M anchor
      (EdgeIndexedMultigraph.cyclicPrev C.size C.size_pos start) = false := by
    have hrootInc : M.Inc x (C.incoming M start) := by
      rw [EdgeIndexedMultigraph.Inc, C.ends_incoming, Sym2.mem_iff]
      exact Or.inr hstartVertex.symm
    rcases c.cutRootEdge_other_endpoint hc cover q cut anchor hcycleAnchor
        hcopyLast (C.incoming M start) hrootInc with h | h
    · obtain ⟨z, hzx, hzinc, hzanchor⟩ := h
      exact C.anchorEdge_prev_unmarked M anchor start x z hstartVertex hzx
        hzinc hzanchor
    · obtain ⟨z, hzx, hzinc, hzdegree⟩ := h
      exact C.degreeTwo_prev_unmarked M anchor hanchorInc start x z
        hstartVertex hzx hzinc hzdegree
  apply C.anchorMarked_toHasStrongSquareCycle M G x {z | z ∈ c.support}
    anchor hanchorInc
    hdegree (c.cutAugmentedTrailMultigraph_square_adj cover q cut)
    (c.cutAugmentedTrailMultigraph_cycle_edge cover q cut) start
    hstartVertex hstart hedge hnext hprev
  · change x ∈ c.support
    simpa only [c.getVert_zero] using c.getVert_mem_support 0
  · exact hcard

/-- The three parity-preparation cases all lift to a rooted Hamiltonian cycle in the graph
square. -/
private theorem hasStrongSquareCycle_of_componentTrailCovers
    [Fintype V] [DecidableEq V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] (k : Fin c.length) (hk0 : k ≠ 0)
    (hbound : c.IsBoundVertex (c.getVert k))
    (hcard : 3 ≤ Fintype.card V) : G.HasStrongSquareCycle x := by
  let q := c.cycleEulerizationCompletion hc cover
  have hlastCases : q.copies (cycleLastIndex c.length) = 0 ∨
      q.copies (cycleLastIndex c.length) = 1 := by
    have hlt := q.copies_lt_two (cycleLastIndex c.length)
    omega
  rcases hlastCases with hlast | hlast
  · have hkCases : q.copies k = 0 ∨ q.copies k = 1 := by
      have hlt := q.copies_lt_two k
      omega
    rcases hkCases with hk | hk
    · exact c.hasStrongSquareCycle_of_split hc cover k hk0 hbound hlast hk hcard
    · let cut : ActiveCycleCopy q := ⟨k, hk⟩
      exact c.hasStrongSquareCycle_of_cutSplit hc cover cut hlast hcard
  · exact c.hasStrongSquareCycle_of_forwardLastCut hc cover hlast hcard

end Walk

end SimpleGraph

/-! ## FleischnerStrong -/


namespace SimpleGraph

universe u

private theorem IsVertexConnected.hasStrongSquareCycle_of_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2)
    (hcard : Fintype.card V = 3) (x : V) : G.HasStrongSquareCycle x := by
  classical
  obtain ⟨c, hc⟩ := hG.exists_cycle_through x
  have hlength_le : c.length ≤ Fintype.card V := by
    have htail := List.Nodup.length_le_card hc.isPath_tail.support_nodup
    rw [c.tail.length_support, Walk.length_tail] at htail
    have hpos : 0 < c.length := Walk.not_nil_iff_lt_length.mp hc.not_nil
    omega
  have hlength : c.length = Fintype.card V := by
    have := hc.three_le_length
    omega
  let f : G →g G.square := {
    toFun v := v
    map_rel' h := ⟨G.ne_of_adj h, Or.inl h⟩ }
  let p : G.square.Walk x x := c.map f
  have hhc : c.IsHamiltonianCycle :=
    Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, hlength⟩
  have hp : p.IsHamiltonianCycle := by
    apply hhc.map
    exact Function.bijective_id
  refine ⟨p, hp, ?_, ?_⟩
  · have hsnd : p.snd = c.snd := by
      simp only [p, Walk.snd, Walk.getVert_map]
      rfl
    rw [hsnd]
    exact c.adj_snd hc.not_nil
  · have hpenultimate : p.penultimate = c.penultimate := by
      simp only [p, Walk.penultimate, Walk.length_map, Walk.getVert_map]
      rfl
    rw [hpenultimate]
    exact c.adj_penultimate hc.not_nil

/-- The vertex-rooted strengthening of Fleischner's theorem, indexed by the number of
vertices for strong induction. -/
private theorem IsVertexConnected.hasStrongSquareCycle_card
    (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2) (hcard : Fintype.card V = n) (x : V) :
    G.HasStrongSquareCycle x := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      classical
      have hn3 : 3 ≤ n := by
        have := hG.card_gt
        omega
      by_cases hn : n = 3
      · apply hG.hasStrongSquareCycle_of_card_eq_three
        omega
      · obtain ⟨c, hc, y, hyx, hbound⟩ := hG.exists_cycle_bound_vertex x
        have hclength : 0 < c.length := lt_of_lt_of_le (by omega) hc.three_le_length
        let _ : NeZero c.length := ⟨Nat.ne_of_gt hclength⟩
        let k := hc.finLengthEquivSupport.symm ⟨y, hbound.1⟩
        have hky : c.getVert k = y := by
          apply (hc.finLengthEquivSupport_apply k).symm.trans
          simpa only [k] using congrArg Subtype.val
            (hc.finLengthEquivSupport.apply_symm_apply ⟨y, hbound.1⟩)
        have hk0 : k ≠ 0 := by
          intro hk
          apply hyx
          have hkval : k.val = 0 := congrArg Fin.val hk
          calc
            y = c.getVert k := hky.symm
            _ = c.getVert 0 := congrArg c.getVert hkval
            _ = x := c.getVert_zero
        have hboundK : c.IsBoundVertex (c.getVert k) := hky ▸ hbound
        let cover : (D : c.outsideGraph.ConnectedComponent) →
            c.ComponentTrailCover D := fun D ↦ Classical.choice (by
          by_cases hD : (c.componentVertices D).ncard = 1
          · exact SimpleGraph.Walk.IsVertexConnected.singletonComponentTrailCover
              hG c D hD
          · have hDpos : 0 < (c.componentVertices D).ncard :=
              (Set.ncard_pos).mpr (c.componentVertices_nonempty D)
            have hDtwo : 1 < (c.componentVertices D).ncard := by omega
            let _ : Fintype (c.componentVertices D) := Fintype.ofFinite _
            have hcontract := hc.component_contractOutside_isVertexConnected hG D hDtwo
            have hltCard : Fintype.card (Option (c.componentVertices D)) < n := by
              have hlt := hc.card_component_contractOutside_lt D
              rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard] at hlt
              exact hlt
            have hstrong : (G.contractOutside (c.componentVertices D)).HasStrongSquareCycle
                none := by
              apply ih (Fintype.card (Option (c.componentVertices D))) hltCard
                hcontract rfl
            exact SimpleGraph.Walk.ComponentTrailCover.exists_of_contractOutside_strongCycle
              D hstrong)
        apply c.hasStrongSquareCycle_of_componentTrailCovers hc cover k hk0 hboundK
        omega

/-- **Strengthened Fleischner theorem.** Let $G$ be a finite simple graph that is
2-vertex-connected, that is, $G$ has at least three vertices and stays connected after deleting at
most one vertex. Let $G^2$ be the square of $G$: the graph on the same vertices in which two
distinct vertices are adjacent if and only if they are adjacent in $G$ or have a common neighbour
in $G$. Then for every vertex $x$ of $G$, the graph $G^2$ has a Hamiltonian cycle whose two edges
at $x$ are edges of $G$. -/
public theorem IsVertexConnected.hasStrongSquareCycle
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2) (x : V) : G.HasStrongSquareCycle x :=
  hG.hasStrongSquareCycle_card (Fintype.card V) rfl x

end SimpleGraph
