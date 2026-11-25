/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Goodman's lower bound on the number of triangles

For a finite simple graph `G` with `n` vertices and `m` edges, Goodman's bound says that the
number `T` of triangles satisfies `3 n T ≥ m (4 m - n ^ 2)`. In homomorphism densities
`t(K₂, G) = 2 m / n ^ 2` and `t(K₃, G) = 6 T / n ^ 3` this reads
`t(K₃, G) ≥ t(K₂, G) (2 t(K₂, G) - 1)`, the finite counterpart of the inequality
`K₃ ≥ ρ (2 ρ - 1)` that Razborov derives in the flag algebra of graphs and attributes to Goodman
(Razborov, *Flag algebras*, J. Symbolic Logic 72 (2007), 1239-1282, Example 11 in the author's
version at people.cs.uchicago.edu/~razborov/files/flag.pdf). The induced-density form
`T / C(n, 3) ≥ ρ (2 ρ - 1)` with `ρ = m / C(n, 2)` holds only in the limit `n → ∞`: the
four-cycle violates it (see the tests).

The proof is the classical one: for every ordered edge `(u, v)` the common neighbourhood of `u`
and `v` has at least `deg u + deg v - n` vertices, and summing over ordered edges gives
`6 T + 2 m n ≥ 2 ∑ deg² ≥ 8 m ² / n` by the Cauchy-Schwarz inequality.

We count triangles as ordered triples (`orderedTriangles`, the homomorphisms from `K₃`), prove
the bound in that form (`goodman_orderedTriangles`), relate ordered triples to the `3`-cliques
(`card_orderedTriangles_eq_six_mul`), and deduce the classical form (`goodman`) and Mantel's
theorem (`four_mul_card_edgeFinset_le_sq_of_cliqueFree_three`).

## References

* A. W. Goodman, *On sets of acquaintances and strangers at any party*, Amer. Math. Monthly 66
  (1959), 778-783.
* A. A. Razborov, *Flag algebras*, J. Symbolic Logic 72 (2007), 1239-1282 (Example 11 in the
  author's version).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound

open Finset

variable {V : Type*} [Fintype V] (G : _root_.SimpleGraph V) [DecidableRel G.Adj]

/-- **Ordered triangles of a graph.** The ordered triples `(u, v, w)` of vertices of a finite
simple graph `G` that are pairwise adjacent. They are the homomorphisms from the triangle `K₃`
to `G`, so their number is `6` times the number of triangles
(`card_orderedTriangles_eq_six_mul`), and `#(orderedTriangles G) / n ^ 3` is the homomorphism
density `t(K₃, G)` of Lovász's graph-limit theory. -/
def orderedTriangles : Finset (V × V × V) :=
  {p | G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.1 p.2.2}

/-- **Membership in the ordered triangles.** `(u, v, w)` is an ordered triangle of `G` exactly
when `u`, `v` and `w` are pairwise adjacent. -/
@[simp] theorem mem_orderedTriangles {p : V × V × V} :
    p ∈ orderedTriangles G ↔ G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.1 p.2.2 := by
  simp [orderedTriangles]

variable [DecidableEq V] in
/-- **Ordered triangles through common neighbourhoods.** The number of ordered triangles of `G`
is the sum, over ordered pairs `(u, v)` of adjacent vertices, of the number of common
neighbours of `u` and `v`. -/
theorem card_orderedTriangles :
    #(orderedTriangles G) =
      ∑ u, ∑ v ∈ G.neighborFinset u, #(G.neighborFinset u ∩ G.neighborFinset v) := by
  classical
  unfold orderedTriangles
  rw [card_filter, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun u _ => ?_
  rw [← univ_product_univ, sum_product, ← sum_filter_add_sum_filter_not univ (G.Adj u)]
  rw [show ∑ v ∈ univ with ¬ G.Adj u v, ∑ w, (if G.Adj (u, v, w).1 (u, v, w).2.1 ∧
      G.Adj (u, v, w).2.1 (u, v, w).2.2 ∧ G.Adj (u, v, w).1 (u, v, w).2.2 then 1 else 0) = 0 from
    sum_eq_zero fun v hv => sum_eq_zero fun w _ => by
      simp only [mem_filter] at hv
      simp [hv.2]]
  rw [add_zero, ← G.neighborFinset_eq_filter]
  refine sum_congr rfl fun v hv => ?_
  rw [_root_.SimpleGraph.mem_neighborFinset] at hv
  have hset : G.neighborFinset u ∩ G.neighborFinset v =
      univ.filter (fun w => G.Adj v w ∧ G.Adj u w) := by
    ext w; simp [and_comm]
  rw [hset, card_filter]
  simp [hv]

variable [DecidableEq V] in
/-- **Common neighbourhood bound.** For all vertices `u` and `v` of a finite simple graph on `n`
vertices, `deg u + deg v ≤ |N(u) ∩ N(v)| + n`, because `N(u) ∪ N(v)` has at most `n`
vertices. -/
theorem degree_add_degree_le (u v : V) :
    G.degree u + G.degree v ≤ #(G.neighborFinset u ∩ G.neighborFinset v) + Fintype.card V := by
  rw [← G.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree,
    ← card_union_add_card_inter, add_comm]
  exact Nat.add_le_add_left (card_le_univ _) _

/-- Summing a function of the second endpoint over ordered edges is summing it against the
degree. -/
private theorem sum_neighbor_degree :
    ∑ u, ∑ v ∈ G.neighborFinset u, G.degree v = ∑ v, G.degree v * G.degree v := by
  classical
  have h : ∀ u, ∑ v ∈ G.neighborFinset u, G.degree v =
      ∑ v, if G.Adj u v then G.degree v else 0 := fun u => by
    rw [G.neighborFinset_eq_filter, sum_filter]
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  congr 1
  ext u; simp [G.adj_comm]

/-- **Goodman's bound for ordered triangles.** For a finite simple graph `G` with `n` vertices,
`m` edges and `T₀` ordered triangles (`orderedTriangles`), `8 m ^ 2 ≤ n T₀ + 2 m n ^ 2`. With
`T₀ = 6 T` this is Goodman's inequality `3 n T ≥ m (4 m - n ^ 2)` (`goodman`). -/
theorem goodman_orderedTriangles_nat :
    8 * #G.edgeFinset ^ 2 ≤
      Fintype.card V * #(orderedTriangles G) + 2 * #G.edgeFinset * Fintype.card V ^ 2 := by
  classical
  set n := Fintype.card V
  set m := #G.edgeFinset
  -- Summing the common-neighbourhood bound over ordered edges.
  have hsum : 2 * ∑ v, G.degree v ^ 2 ≤ #(orderedTriangles G) + 2 * m * n := by
    have h1 : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) ≤
        ∑ u, ∑ v ∈ G.neighborFinset u,
          (#(G.neighborFinset u ∩ G.neighborFinset v) + n) :=
      sum_le_sum fun u _ => sum_le_sum fun v _ => degree_add_degree_le G u v
    have hl : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) =
        2 * ∑ v, G.degree v ^ 2 := by
      simp_rw [sum_add_distrib, sum_neighbor_degree, sum_const, G.card_neighborFinset_eq_degree,
        smul_eq_mul, sq]
      ring
    have hr : ∑ u, ∑ v ∈ G.neighborFinset u,
        (#(G.neighborFinset u ∩ G.neighborFinset v) + n) = #(orderedTriangles G) + 2 * m * n := by
      simp_rw [sum_add_distrib, ← card_orderedTriangles, sum_const,
        G.card_neighborFinset_eq_degree, smul_eq_mul, ← sum_mul, G.sum_degrees_eq_twice_card_edges]
      rfl
    omega
  -- Cauchy-Schwarz: `(∑ deg) ^ 2 ≤ n ∑ deg ^ 2`.
  have hcs : (2 * m) ^ 2 ≤ n * ∑ v, G.degree v ^ 2 := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := fun v => G.degree v)
  nlinarith [hsum, hcs]

/-- **Goodman's bound in homomorphism-count form.** For a finite simple graph `G` with `n`
vertices, `m` edges and `T₀` ordered triangles, `2 m (4 m - n ^ 2) ≤ n T₀` (as integers).
Dividing by `n ^ 4` gives `t(K₃, G) ≥ t(K₂, G) (2 t(K₂, G) - 1)` for the homomorphism densities
`t(K₂, G) = 2 m / n ^ 2` and `t(K₃, G) = T₀ / n ^ 3`, a finite form of the flag-algebra
inequality `K₃ ≥ ρ (2 ρ - 1)` (Razborov, *Flag algebras*, J. Symbolic Logic 72 (2007),
Example 11 in the author's version). -/
theorem goodman_orderedTriangles :
    2 * (#G.edgeFinset : ℤ) * (4 * #G.edgeFinset - Fintype.card V ^ 2) ≤
      Fintype.card V * #(orderedTriangles G) := by
  have := goodman_orderedTriangles_nat G
  have h : ((8 * #G.edgeFinset ^ 2 : ℕ) : ℤ) ≤
      ((Fintype.card V * #(orderedTriangles G) + 2 * #G.edgeFinset * Fintype.card V ^ 2 : ℕ) : ℤ) :=
    by exact_mod_cast this
  push_cast at h
  nlinarith [h]

variable [DecidableEq V] in
/-- The fibre of the vertex-set map over one triangle `{a, b, c}`: its six orderings. -/
private theorem fibre_eq {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    (orderedTriangles G).filter (fun p => ({p.1, p.2.1, p.2.2} : Finset V) = {a, b, c}) =
      {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} := by
  ext ⟨x, y, z⟩
  simp only [orderedTriangles, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hxy, hyz, hxz⟩, hs⟩
    have hx : x ∈ ({a, b, c} : Finset V) := hs ▸ by simp
    have hy : y ∈ ({a, b, c} : Finset V) := hs ▸ by simp
    have hz : z ∈ ({a, b, c} : Finset V) := hs ▸ by simp
    simp only [mem_insert, mem_singleton] at hx hy hz
    have h1 := G.ne_of_adj hxy
    have h2 := G.ne_of_adj hyz
    have h3 := G.ne_of_adj hxz
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;> simp_all
  · have hba := hab.symm
    have hca := hac.symm
    have hcb := hbc.symm
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      refine ⟨by simp_all, ?_⟩ <;> ext w <;> simp only [mem_insert, mem_singleton] <;> tauto

variable [DecidableEq V] in
/-- **Ordered triangles and triangles.** A finite simple graph has exactly six times as many
ordered triangles (`orderedTriangles`) as triangles (`3`-cliques): each triangle `{a, b, c}`
has `3! = 6` orderings. -/
theorem card_orderedTriangles_eq_six_mul :
    #(orderedTriangles G) = 6 * #(G.cliqueFinset 3) := by
  rw [card_eq_sum_card_fiberwise (f := fun p => ({p.1, p.2.1, p.2.2} : Finset V))
    (t := G.cliqueFinset 3)]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s hs => ?_
    rw [_root_.SimpleGraph.mem_cliqueFinset_iff, _root_.SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    rw [fibre_eq G hab hac hbc]
    have h1 := G.ne_of_adj hab
    have h2 := G.ne_of_adj hac
    have h3 := G.ne_of_adj hbc
    simp [card_insert_of_notMem, h1, h2, h3, h1.symm, h2.symm, h3.symm]
  · rintro ⟨x, y, z⟩ hp
    rw [mem_coe, mem_orderedTriangles] at hp
    simp only [mem_coe, _root_.SimpleGraph.mem_cliqueFinset_iff]
    exact _root_.SimpleGraph.is3Clique_triple_iff.mpr ⟨hp.1, hp.2.2, hp.2.1⟩

variable [DecidableEq V] in
/-- **Goodman's bound on the number of triangles.** A finite simple graph `G` with `n` vertices,
`m` edges and `T` triangles (`3`-cliques) satisfies `m (4 m - n ^ 2) ≤ 3 n T` (as integers).
The bound is due to A. W. Goodman (*On sets of acquaintances and strangers at any party*,
Amer. Math. Monthly 66 (1959), 778-783); Razborov derives its limit form `K₃ ≥ ρ (2 ρ - 1)` in
the flag algebra of graphs and attributes it to Goodman (*Flag algebras*, J. Symbolic Logic 72
(2007), Example 11 in the author's version). In particular a graph with more than `n ^ 2 / 4`
edges has a triangle. -/
theorem goodman :
    (#G.edgeFinset : ℤ) * (4 * #G.edgeFinset - Fintype.card V ^ 2) ≤
      3 * Fintype.card V * #(G.cliqueFinset 3) := by
  have h := goodman_orderedTriangles G
  rw [card_orderedTriangles_eq_six_mul] at h
  push_cast at h
  linarith

/-- **Mantel's theorem from Goodman's bound.** A triangle-free finite simple graph with `n`
vertices has at most `n ^ 2 / 4` edges: `4 m ≤ n ^ 2` (W. Mantel, Wiskundige Opgaven 10 (1907),
60-61). The proof is the flag-algebra one: Goodman's bound with no triangles forces
`m (4 m - n ^ 2) ≤ 0`. In Mathlib the bound is a two-line corollary of Turán's theorem:
`SimpleGraph.CliqueFree.card_edgeFinset_le` with `r = 2` gives `m ≤ turanNumber n 2`, and
`SimpleGraph.turanNumber_two` evaluates it as `n ^ 2 / 4`; this version records the
flag-algebra proof. -/
theorem four_mul_card_edgeFinset_le_sq_of_cliqueFree_three (h : G.CliqueFree 3) :
    4 * #G.edgeFinset ≤ Fintype.card V ^ 2 := by
  classical
  have hg := goodman G
  rw [G.cliqueFinset_eq_empty_iff.mpr h, card_empty] at hg
  push_cast at hg
  rcases Nat.eq_zero_or_pos #G.edgeFinset with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℤ) < #G.edgeFinset := by exact_mod_cast hpos
    have : (4 * #G.edgeFinset : ℤ) ≤ Fintype.card V ^ 2 := by nlinarith
    exact_mod_cast this

end MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound
