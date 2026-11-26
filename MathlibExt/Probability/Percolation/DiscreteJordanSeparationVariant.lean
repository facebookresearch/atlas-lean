/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourAnchor
public import MathlibExt.Probability.Percolation.DiscreteJordanSeparationFalse

/-!
# A corrected discrete Jordan separation property, and its refutation

`StatMech.Percolation.DiscreteJordanSeparation` (any two connected faces of the face-boundary
graph of a finite set lie on a common cycle) fails trivially for an isolated face
(`djsf_djs_is_false`). The variant `djfx_DiscreteJordanSeparation'` adds the hypothesis that the
first face has a neighbour. This variant is also false: for the two primal sites
`{(0, 0), (1, 1)}`, which touch at a corner, the face-boundary graph is two 4-cycles sharing the
face `(0, 0)`, so faces on different 4-cycles are connected but lie on no common cycle
(`not_djfx_DiscreteJordanSeparation'`). The graph-theoretic reason is that a face-boundary graph
is an even-degree graph, and even-degree graphs need not be 2-connected.

What does hold: every edge of the face-boundary graph of a finite set lies on a cycle
(`djfx_faceBoundaryGraph_edgeCycle`).

## Main definitions

* `StatMech.Percolation.djfx_DiscreteJordanSeparation'`: the corrected separation property.
* `StatMech.Percolation.djfx_bowtie`: the counterexample `{(0, 0), (1, 1)}`.

## Main results

* `StatMech.Percolation.djfx_faceBoundaryGraph_edgeCycle`: each edge lies on a cycle.
* `StatMech.Percolation.not_djfx_DiscreteJordanSeparation'`: the corrected property is false.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- The corrected discrete Jordan separation property: in the face-boundary graph of a finite set
`K`, if the face `a` has a neighbour and `b` is reachable from `a`, then some cycle through `a`
contains `b`. It is false (`not_djfx_DiscreteJordanSeparation'`). -/
def djfx_DiscreteJordanSeparation' : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → ∀ {a b : Site 2},
    (∃ a' : Site 2, (faceBoundaryGraph K).Adj a a') →
    (faceBoundaryGraph K).Reachable a b →
      ∃ c : (faceBoundaryGraph K).Walk a a, c.IsCycle ∧ b ∈ c.support

/-- The conclusion of `djfx_DiscreteJordanSeparation'` holds for `K = ∅`, vacuously: the
face-boundary graph of `∅` has no edges. -/
theorem djfx_separation'_holds_empty {a b : Site 2}
    (hpos : ∃ a' : Site 2, (faceBoundaryGraph (∅ : Set (Site 2))).Adj a a')
    (_hreach : (faceBoundaryGraph (∅ : Set (Site 2))).Reachable a b) :
    ∃ c : (faceBoundaryGraph (∅ : Set (Site 2))).Walk a a, c.IsCycle ∧ b ∈ c.support := by
  obtain ⟨a', hadj⟩ := hpos
  exact absurd hadj (djsf_faceBoundaryGraph_empty_not_adj a a')

/-- Every edge `vw` of the face-boundary graph of a finite set lies on a cycle based at `v`: the
graph has finite support and all degrees even. -/
theorem djfx_faceBoundaryGraph_edgeCycle (K : Set (Site 2)) (hK : K.Finite) {v w : Site 2}
    (hadj : (faceBoundaryGraph K).Adj v w) :
    ∃ c : (faceBoundaryGraph K).Walk v v, c.IsCycle ∧ w ∈ c.support := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph K hK
  obtain ⟨u, p, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph K) T hT (degree_faceBoundaryGraph_even K) hadj
  have hv : v ∈ p.support := p.fst_mem_support_of_mem_edges hedge
  have hw : w ∈ p.support := p.snd_mem_support_of_mem_edges hedge
  exact ⟨p.rotate v hv, hcyc.rotate hv, (Walk.mem_support_rotate_iff p v hv).mpr hw⟩

/-- A face with a neighbour in the face-boundary graph of a finite set lies on a cycle. -/
theorem djfx_edgeCycle_self (K : Set (Site 2)) (hK : K.Finite) {v w : Site 2}
    (hadj : (faceBoundaryGraph K).Adj v w) :
    ∃ c : (faceBoundaryGraph K).Walk v v, c.IsCycle ∧ v ∈ c.support := by
  obtain ⟨c, hcyc, _⟩ := djfx_faceBoundaryGraph_edgeCycle K hK hadj
  exact ⟨c, hcyc, c.start_mem_support⟩

/-- For a finite origin cluster, the upper exit face has a neighbour (the lower exit face) in the
face-boundary graph of the cluster. -/
theorem djfx_exitFaceUp_edge_endpoint (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ a' : Site 2,
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj (exitFaceUp (ω := ω) hfin) a' :=
  ⟨exitFaceDown (ω := ω) hfin, exitFaces_faceBoundaryGraph_adj (ω := ω) hfin⟩

/-- Two primal sites touching at a corner: `{(0, 0), (1, 1)}`. Its face-boundary graph is two
4-cycles of faces sharing the face `(0, 0)`. -/
def djfx_bowtie : Set (Site 2) := {![0, 0], ![1, 1]}

/-- Membership in `djfx_bowtie` in coordinates. -/
theorem djfx_mem_bowtie {x : Site 2} :
    x ∈ djfx_bowtie ↔ (x 0 = 0 ∧ x 1 = 0) ∨ (x 0 = 1 ∧ x 1 = 1) := by
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · left; funext i; fin_cases i <;> simp [h0, h1]
    · right; funext i; fin_cases i <;> simp [h0, h1]

/-- Adjacency in the face-boundary graph of `djfx_bowtie`, unfolded into coordinates. -/
theorem djfx_bowtie_adj {x z : Site 2} (h : (faceBoundaryGraph djfx_bowtie).Adj x z) :
    (x 0 - z 0).natAbs + (x 1 - z 1).natAbs = 1 ∧
      (if x 0 = z 0 then
        ((x 0 = 0 ∧ max (x 1) (z 1) = 0) ∨ (x 0 = 1 ∧ max (x 1) (z 1) = 1) ↔
          ¬ ((x 0 + 1 = 0 ∧ max (x 1) (z 1) = 0) ∨ (x 0 + 1 = 1 ∧ max (x 1) (z 1) = 1)))
      else
        ((max (x 0) (z 0) = 0 ∧ x 1 = 0) ∨ (max (x 0) (z 0) = 1 ∧ x 1 = 1) ↔
          ¬ ((max (x 0) (z 0) = 0 ∧ x 1 + 1 = 0) ∨ (max (x 0) (z 0) = 1 ∧ x 1 + 1 = 1)))) := by
  obtain ⟨hadj, hbd⟩ := h
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  refine ⟨hadj, ?_⟩
  unfold sharedPrimalEdge at hbd
  split_ifs at hbd ⊢ with hx
  · rw [bdEdge_mk, djfx_mem_bowtie, djfx_mem_bowtie] at hbd; simpa using hbd
  · rw [bdEdge_mk, djfx_mem_bowtie, djfx_mem_bowtie] at hbd; simpa using hbd

/-- The faces around the primal site `(0, 0)`. -/
def djfx_petal : Set (Site 2) := {x | -1 ≤ x 0 ∧ x 0 ≤ 0 ∧ -1 ≤ x 1 ∧ x 1 ≤ 0}

/-- A face of `djfx_petal` other than `(0, 0)` has all its neighbours in the face-boundary graph
of `djfx_bowtie` inside `djfx_petal`. -/
theorem djfx_petal_closed {x z : Site 2} (hx : x ∈ djfx_petal) (hx0 : ¬ (x 0 = 0 ∧ x 1 = 0))
    (h : (faceBoundaryGraph djfx_bowtie).Adj x z) : z ∈ djfx_petal := by
  obtain ⟨hadj, hbd⟩ := djfx_bowtie_adj h
  simp only [djfx_petal, Set.mem_ofPred_eq] at hx ⊢
  split_ifs at hbd <;> omega

/-- Every walk in the face-boundary graph of `djfx_bowtie` from inside `djfx_petal` to outside it
passes through the face `(0, 0)`: that face is a cut vertex. -/
theorem djfx_walk_hits {x y : Site 2} (w : (faceBoundaryGraph djfx_bowtie).Walk x y)
    (hx : x ∈ djfx_petal) (hy : y ∉ djfx_petal) : ∃ v ∈ w.support, v 0 = 0 ∧ v 1 = 0 := by
  induction w with
  | nil => exact absurd hx hy
  | @cons x z y h w ih =>
    by_cases hx0 : x 0 = 0 ∧ x 1 = 0
    · exact ⟨x, by simp, hx0⟩
    · obtain ⟨v, hv, hv0⟩ := ih (djfx_petal_closed hx hx0 h) hy
      exact ⟨v, by simp [hv], hv0⟩

/-- Introduction rule for adjacency in the face-boundary graph of `djfx_bowtie`. -/
theorem djfx_bowtie_adj_of {x z : Site 2}
    (h : (hypercubicLattice 2).Adj x z ∧ bdEdge djfx_bowtie (sharedPrimalEdge x z)) :
    (faceBoundaryGraph djfx_bowtie).Adj x z := h

/-- Proves adjacency between explicit faces in the face-boundary graph of `djfx_bowtie`. -/
local macro "djfx_adj" : tactic => `(tactic| (
  refine djfx_bowtie_adj_of ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · unfold sharedPrimalEdge
    split_ifs <;> (rw [bdEdge_mk, djfx_mem_bowtie, djfx_mem_bowtie]; simp_all)))

/-- The corrected discrete Jordan separation property is false. Counterexample: `K = {(0, 0),
(1, 1)}`, `a = (-1, -1)`, `b = (1, 1)`; every walk from `a` to `b` passes through the face
`(0, 0)`, so a closed walk through `a` and `b` visits `(0, 0)` twice and is not a cycle. -/
theorem not_djfx_DiscreteJordanSeparation' : ¬ djfx_DiscreteJordanSeparation' := by
  intro hsep
  have hfin : djfx_bowtie.Finite := (Set.finite_singleton _).insert _
  have e1 : (faceBoundaryGraph djfx_bowtie).Adj ![-1, -1] ![-1, 0] := by djfx_adj
  have e2 : (faceBoundaryGraph djfx_bowtie).Adj ![-1, 0] ![0, 0] := by djfx_adj
  have e3 : (faceBoundaryGraph djfx_bowtie).Adj ![0, 0] ![0, 1] := by djfx_adj
  have e4 : (faceBoundaryGraph djfx_bowtie).Adj ![0, 1] ![1, 1] := by djfx_adj
  have hreach : (faceBoundaryGraph djfx_bowtie).Reachable ![-1, -1] ![1, 1] :=
    e1.reachable.trans (e2.reachable.trans (e3.reachable.trans e4.reachable))
  obtain ⟨c, hcyc, hb⟩ := hsep djfx_bowtie hfin ⟨_, e1⟩ hreach
  have ha : (![-1, -1] : Site 2) ∈ djfx_petal := by simp [djfx_petal]
  have hb' : (![1, 1] : Site 2) ∉ djfx_petal := by simp [djfx_petal]
  set p := c.takeUntil _ hb
  set q := c.dropUntil _ hb
  obtain ⟨v, hvp, hv⟩ := djfx_walk_hits p ha hb'
  obtain ⟨v', hvq, hv'⟩ := djfx_walk_hits q.reverse ha hb'
  rw [Walk.support_reverse, List.mem_reverse] at hvq
  have hvv : v = v' := by funext i; fin_cases i <;> simp [hv, hv']
  subst hvv
  have hnd := hcyc.support_nodup
  rw [← c.take_spec hb, Walk.support_append, List.tail_append_of_ne_nil (by simp)] at hnd
  have h1 : v ∈ p.support.tail := by
    rw [← p.cons_tail_support] at hvp
    rcases List.mem_cons.mp hvp with h | h
    · have := congrFun h 0; simp [hv] at this
    · exact h
  have h2 : v ∈ q.support.tail := by
    rw [← q.cons_tail_support] at hvq
    rcases List.mem_cons.mp hvq with h | h
    · have := congrFun h 0; simp [hv] at this
    · exact h
  exact (List.nodup_append.mp hnd).2.2 _ h1 _ h2 rfl

end Percolation

end StatMech
