/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.TopologicalSort
public import MathlibExt.Probability.Statistics.Measurement.StructuralEquation

/-!
# SEM adapter: DAG-supported coefficient matrices

A coefficient matrix supported on the edges of an acyclic directed graph
(`B i j ≠ 0` only on the edge `j → i`) is nilpotent, and `1 - B` has the
finite inverse `∑ k < card V, B ^ k`. The adapter obtains a topological
order from the executable sort interface and instantiates the existing
structural-equation identities at `ord := order.idxOf`.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

open TopologicalSort MathlibExt.Probability.Statistics.Measurement

namespace SEMAdapter

open TopologicalSort MathlibExt.Probability.Statistics.Measurement

/-- The Fintype carrier has exactly the enumerated vertices: `vertices_nodup`
and `vertices_complete` identify `Finset.univ` with `g.vertices.toFinset`,
so `Fintype.card V = g.vertices.length` (`Finset.card` of a nodup list). -/
theorem card_eq_vertices_length {V : Type*} [DecidableEq V] [Fintype V]
    (g : DirectedAdjacency V) :
    Fintype.card V = g.vertices.length := by
  have huniv : (Finset.univ : Finset V) = g.vertices.toFinset := by
    ext v
    simp [g.vertices_complete v]
  have hcard := congrArg Finset.card huniv
  rw [Finset.card_univ, List.toFinset_card_of_nodup g.vertices_nodup] at hcard
  exact hcard

/-- Acyclicity gives a complete nodup topological order whose length is
the carrier cardinality (length from coverage plus `card_eq_vertices_length`). -/
theorem exists_topologicalOrder {V : Type*} [DecidableEq V]
    [Fintype V] (g : DirectedAdjacency V) (hacyclic : IsAcyclic g) :
    ∃ order : List V, IsTopologicalOrder g order ∧
      order.length = Fintype.card V := by
  -- The executable sort needs a hash instance; any two give the same
  -- acyclicity interface, so use a constant local one and do not leak
  -- `Hashable` into this mathematical statement.
  letI : Hashable V := ⟨fun _ => 0⟩
  obtain ⟨order, hsort⟩ := acyclic_implies_success g hacyclic
  have htopo := success_isTopologicalOrder g order hsort
  refine ⟨order, htopo, ?_⟩
  obtain ⟨hnodup, hcov, _hfwd⟩ := htopo
  have hfin : order.toFinset = g.vertices.toFinset := by
    ext v
    simp [hcov v]
  have h1 := List.toFinset_card_of_nodup hnodup
  have h2 := List.toFinset_card_of_nodup g.vertices_nodup
  have hlen : order.length = g.vertices.length := by
    rw [← h1, ← h2, hfin]
  rw [hlen, ← card_eq_vertices_length g]

/-- Rank bound: every vertex occurs in a complete order, so `List.idxOf`
is below the order length, which is `Fintype.card V`. -/
theorem idxOf_lt_card {V : Type*} [DecidableEq V] [Fintype V]
    (g : DirectedAdjacency V) {order : List V}
    (horder : IsTopologicalOrder g order)
    (hlength : order.length = Fintype.card V) (v : V) :
    order.idxOf v < Fintype.card V := by
  obtain ⟨_, hcov, _⟩ := horder
  have hmem : v ∈ order := by
    rw [hcov v]
    exact g.vertices_complete v
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [hlength] at hlt
  exact hlt

/-- Edge orientation: an edge `j → i` points forward in the order.
This is the third component of `IsTopologicalOrder`, renamed at the
SEM boundary so the transposition convention is stated once, here. -/
theorem idxOf_edge_lt {V : Type*} [DecidableEq V]
    (g : DirectedAdjacency V) {order : List V}
    (horder : IsTopologicalOrder g order) {j i : V}
    (hedge : g.Edge j i) :
    order.idxOf j < order.idxOf i := by
  exact horder.2.2 _ _ hedge

/-- Support transport: nonzero `B i j` is, by hypothesis, supported on
edge `j → i`, hence `ord j < ord i` for `ord := (order.idxOf ·)`. This is
exactly the `hB` shape the MathlibExt identities consume. -/
theorem supported_idxOf_lt {V : Type*} [DecidableEq V] {R : Type*}
    [CommRing R] (g : DirectedAdjacency V) {order : List V}
    (horder : IsTopologicalOrder g order) (B : Matrix V V R)
    (hB : ∀ i j, B i j ≠ 0 → g.Edge j i) (i j : V) (hij : B i j ≠ 0) :
    order.idxOf j < order.idxOf i := by
  exact idxOf_edge_lt g horder (hB i j hij)

/-- Nilpotence corollary: a DAG-supported coefficient matrix satisfies
`B ^ Fintype.card V = 0`. Instantiate
`pow_card_eq_zero_of_topologicalOrder` at `ord := (order.idxOf ·)`. -/
theorem pow_card_eq_zero_of_acyclic {V : Type*} [DecidableEq V]
    [Fintype V] {R : Type*} [CommRing R] (g : DirectedAdjacency V)
    (B : Matrix V V R) (hacyclic : IsAcyclic g)
    (hB : ∀ i j, B i j ≠ 0 → g.Edge j i) :
    B ^ Fintype.card V = 0 := by
  obtain ⟨order, horder, hlength⟩ := exists_topologicalOrder g hacyclic
  exact pow_card_eq_zero_of_topologicalOrder B (fun v => order.idxOf v)
    (fun v => idxOf_lt_card g horder hlength v)
    (fun i j hij => supported_idxOf_lt g horder B hB i j hij)

/-- A DAG-supported linear SEM coefficient matrix over a
finite carrier has finite inverse `(1 - B)⁻¹ = ∑ k < card V, B ^ k`.
`B i j ≠ 0` must be supported on the edge `j → i` (column vertex causes
row vertex); the reverse convention is the transposed test failure below.
Instantiate `inv_one_sub_eq_sum_pow_of_topologicalOrder` at
`ord := (order.idxOf ·)`, with `hord` from `idxOf_lt_card` and `hB` from
`supported_idxOf_lt`. -/
theorem inverse_of_acyclic {V : Type*} [DecidableEq V]
    [Fintype V] {R : Type*} [CommRing R] (g : DirectedAdjacency V)
    (B : Matrix V V R) (hacyclic : IsAcyclic g)
    (hB : ∀ i j, B i j ≠ 0 → g.Edge j i) :
    (1 - B)⁻¹ = ∑ k ∈ Finset.range (Fintype.card V), B ^ k := by
  obtain ⟨order, horder, hlength⟩ := exists_topologicalOrder g hacyclic
  exact inv_one_sub_eq_sum_pow_of_topologicalOrder B (fun v => order.idxOf v)
    (fun v => idxOf_lt_card g horder hlength v)
    (fun i j hij => supported_idxOf_lt g horder B hB i j hij)

end SEMAdapter

end Cslib.Algorithms.Lean
