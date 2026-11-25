/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/905.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the conjecture and the statement that it holds.
-/
module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound

/-!
# Edges in many triangles

The Edwards–Khadzhiivanov–Nikiforov theorem (`conjecture_holds`) gives an edge in at least
$n/6$ triangles in every graph on $n$ vertices with more than $n^2/4$ edges.

For each edge count its common neighbors and the vertices adjacent to neither endpoint.
Each vertex agrees in its adjacency to at least two vertices of any triangle. Summing this
observation over triangles relates the two counts, while summing over edges relates their
difference to the sum of squared degrees.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem905Wanted

/-- **Erdős Problem 905 on edges in many triangles.** The proposition asserts that for every
natural number $n$ and every simple graph $G$ on $n$ vertices with more than $n^2/4$ edges, some
edge of $G$ lies in at least $n/6$ triangles of $G$. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) →
    ∃ e : G.edgeSet, (n : ℝ) / 6 ≤ ((G.trianglesContaining e).card : ℝ)

open Finset
open MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private abbrev common (x y : Fin n) := G.neighborFinset x ∩ G.neighborFinset y

private abbrev neither (x y : Fin n) := (G.neighborFinset x ∪ G.neighborFinset y)ᶜ

private lemma common_le_triangles {x y : Fin n} (hxy : G.Adj x y) :
    (common G x y).card ≤ (G.trianglesContaining ⟨s(x, y), hxy⟩).card := by
  classical
  apply card_le_card_of_injOn (fun z => {x, y, z})
  · intro z hz
    simp only [mem_coe, common, mem_inter, SimpleGraph.mem_neighborFinset] at hz
    simp [SimpleGraph.trianglesContaining, SimpleGraph.is3Clique_triple_iff,
      Sym2.toFinset_mk_eq, hxy, hz.1, hz.2, insert_subset_iff]
  · intro a ha b _ hab
    change ({x, y, a} : Finset _) = {x, y, b} at hab
    have hmem : a ∈ ({x, y, b} : Finset _) := by rw [← hab]; simp
    simp only [mem_coe, common, mem_inter, SimpleGraph.mem_neighborFinset] at ha
    simpa [ha.1.ne.symm, ha.2.ne.symm] using hmem

private lemma degree_identity (x y : Fin n) :
    G.degree x + G.degree y + (neither G x y).card = n + (common G x y).card := by
  have hu := card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  have hc := card_add_card_compl (G.neighborFinset x ∪ G.neighborFinset y)
  simp only [G.card_neighborFinset_eq_degree, Fintype.card_fin] at hu hc
  unfold neither common
  omega

-- Of three adjacency decisions at a vertex, two agree.
private lemma triangle_cover (x y z : Fin n) :
    n ≤ (common G x y).card + (neither G x y).card +
      ((common G y z).card + (neither G y z).card) +
      ((common G z x).card + (neither G z x).card) := by
  let agree (a b : Fin n) := common G a b ∪ neither G a b
  have cover : univ ⊆ (agree x y ∪ agree y z) ∪ agree z x := by
    intro v _
    simp only [agree, common, neither, mem_union, mem_inter, mem_compl]
    tauto
  have bound (a b : Fin n) := card_union_le (common G a b) (neither G a b)
  calc
    n = (univ : Finset (Fin n)).card := by simp
    _ ≤ _ := card_le_card cover
    _ ≤ (agree x y).card + (agree y z).card + (agree z x).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (bound x y) (bound y z)) (bound z x)

-- A cyclic change of the distinguished side preserves the sum over ordered triangles.
private lemma sum_rotate (f : Fin n → Fin n → Fin n → ℕ) :
    ∑ t ∈ orderedTriangles G, f t.2.1 t.2.2 t.1 =
      ∑ t ∈ orderedTriangles G, f t.1 t.2.1 t.2.2 := by
  apply sum_nbij' (fun (x, y, z) => (y, z, x)) (fun (x, y, z) => (z, x, y))
  · rintro ⟨x, y, z⟩ ht
    obtain ⟨hxy, hyz, hxz⟩ := (mem_orderedTriangles G).mp ht
    exact (mem_orderedTriangles G).mpr ⟨hyz, hxz.symm, hxy.symm⟩
  · rintro ⟨x, y, z⟩ ht
    obtain ⟨hxy, hyz, hxz⟩ := (mem_orderedTriangles G).mp ht
    exact (mem_orderedTriangles G).mpr ⟨hxz.symm, hxy, hyz.symm⟩
  all_goals intros; rfl

-- Count the third vertex while keeping a weight on the first two.
private lemma sum_triangle_weight (f : Fin n → Fin n → ℕ) :
    ∑ t ∈ orderedTriangles G, f t.1 t.2.1 =
      ∑ x, ∑ y ∈ G.neighborFinset x, (common G x y).card * f x y := by
  rw [orderedTriangles, sum_filter, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [← univ_product_univ, sum_product, G.neighborFinset_eq_filter, sum_filter]
  refine sum_congr rfl fun y _ => ?_
  by_cases hxy : G.Adj x y
  · have hc : common G x y = univ.filter (fun z => G.Adj y z ∧ G.Adj x z) := by
      ext z
      simp [common, and_comm]
    simp [hxy, hc, ← sum_filter, sum_const]
  · simp [hxy]

private lemma orderedTriangles_le_sum_neither (hn : 0 < n)
    (hbook : ∀ x y, G.Adj x y → 6 * (common G x y).card ≤ n) :
    (orderedTriangles G).card ≤ ∑ x, ∑ y ∈ G.neighborFinset x, (neither G x y).card := by
  let f (x y : Fin n) := (neither G x y).card
  have local_bound (t : Fin n × Fin n × Fin n) (ht : t ∈ orderedTriangles G) :
      n ≤ 2 * (f t.1 t.2.1 + f t.2.1 t.2.2 + f t.2.2 t.1) := by
    obtain ⟨x, y, z⟩ := t
    obtain ⟨hxy, hyz, hxz⟩ := (mem_orderedTriangles G).mp ht
    dsimp [f]
    linarith only [triangle_cover G x y z, hbook x y hxy, hbook y z hyz, hbook z x hxz.symm]
  have htotal := sum_le_sum local_bound
  simp only [sum_const, smul_eq_mul, ← mul_sum, sum_add_distrib] at htotal
  have hrot := sum_rotate G (fun x y _ => f x y)
  have hrot' := sum_rotate G (fun _ y z => f y z)
  rw [hrot', hrot, sum_triangle_weight] at htotal
  have hweighted : ∑ x, ∑ y ∈ G.neighborFinset x, (6 * (common G x y).card) * f x y ≤
      ∑ x, ∑ y ∈ G.neighborFinset x, n * f x y := by
    refine sum_le_sum fun x _ => sum_le_sum fun y hy => ?_
    exact Nat.mul_le_mul_right _ (hbook x y ((G.mem_neighborFinset _ _).mp hy))
  simp only [mul_assoc, ← mul_sum] at hweighted
  apply Nat.le_of_mul_le_mul_left _ hn
  rw [mul_comm n (orderedTriangles G).card]
  linarith only [htotal, hweighted]

-- The same difference of counts, summed over edges, measures the degree second moment.
private lemma sum_degree_sq_le (hcount : (orderedTriangles G).card ≤
    ∑ x, ∑ y ∈ G.neighborFinset x, (neither G x y).card) :
    ∑ x, G.degree x ^ 2 ≤ n * G.edgeFinset.card := by
  have hswap : ∑ x, ∑ y ∈ G.neighborFinset x, G.degree y = ∑ x, G.degree x ^ 2 := by
    simp_rw [G.neighborFinset_eq_filter, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp_rw [G.adj_comm _ y, ← sum_filter, ← G.neighborFinset_eq_filter,
      sum_const, G.card_neighborFinset_eq_degree, smul_eq_mul, sq]
  have hid := sum_congr (s₁ := univ) rfl fun x _ =>
    sum_congr (s₁ := G.neighborFinset x) rfl fun y _ => degree_identity G x y
  simp only [sum_add_distrib, sum_const, G.card_neighborFinset_eq_degree, smul_eq_mul, hswap,
    ← card_orderedTriangles, ← sum_mul, G.sum_degrees_eq_twice_card_edges] at hid
  simp only [← sq] at hid
  linarith only [hid, hcount]

/--
**Edwards–Khadzhiivanov–Nikiforov theorem on edges in many triangles.** For every natural number
$n$, every simple graph $G$ on $n$ vertices with more than $n^2/4$ edges has an edge that lies in
at least $n/6$ triangles of $G$.

This was proved independently by Edwards and by Khadzhiivanov and Nikiforov, and answers Erdős
Problem 905 affirmatively.

Source: External Lean proof of Erdős Problem 905,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos905.lean.
Moved from `OpenConjectures/Combinatorics/ErdosProblem905`.
-/
theorem conjecture_holds : conjecture := by
  intro n G _ hdense
  have hd : n ^ 2 < 4 * G.edgeFinset.card := by
    exact_mod_cast (show (n : ℝ) ^ 2 < 4 * G.edgeFinset.card by linarith)
  have hm : 0 < G.edgeFinset.card := by omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun x => G.degree x)
  rw [G.sum_degrees_eq_twice_card_edges, card_univ, Fintype.card_fin] at hcs
  have hn : 0 < n := Nat.pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hcs)
  by_contra! hsmall
  have hbook (x y : Fin n) (hxy : G.Adj x y) : 6 * (common G x y).card ≤ n := by
    have ht := hsmall ⟨s(x, y), hxy⟩
    have hc : ((common G x y).card : ℝ) ≤
        (G.trianglesContaining ⟨s(x, y), hxy⟩).card := by exact_mod_cast common_le_triangles G hxy
    exact_mod_cast (show 6 * ((common G x y).card : ℝ) ≤ n by linarith)
  have hsq := sum_degree_sq_le G (orderedTriangles_le_sum_neither G hn hbook)
  nlinarith only [hcs, Nat.mul_le_mul_left n hsq, Nat.mul_lt_mul_of_pos_left hd hm]

end MathlibExt.Combinatorics.ErdosProblem905Wanted
