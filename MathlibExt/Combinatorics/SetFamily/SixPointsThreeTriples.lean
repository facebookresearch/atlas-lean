/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The Ruzsa–Szemerédi (6, 3) theorem

We prove that the (6, 3) extremal number is subquadratic by applying triangle removal
to the graph formed by the pairs lying in triples.

Source: T. F. Bloom, Erdős Problems, Problem #716, https://www.erdosproblems.com/716 (status PROVED
(LEAN)). UnsolvedMath record UM-30006989 (`EP-716`), dataset ulamai/UnsolvedMath v1.8.0.

A `3`-uniform hypergraph on `{1, …, n}` contains a member of the forbidden family iff some `6`
vertices carry `3` of its edges. For `n < 6`, the convention using at most six vertices can differ
from the literal extremal number, which has no effect on the limit. Compared with the
formal-conjectures statement `ErdosProblems/716.lean` (equivalent; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SixPointsThreeTriplesErdosProblem716Wanted

open Filter Topology

/-- **The (6, 3) extremal number.** For $n \in \mathbb{N}$, $\mathrm{ex}_3(n)$ is the largest
number of $3$-element subsets of $\{1, \dots, n\}$ such that every set of at most $6$ of these
points contains at most $2$ of the chosen subsets.

For $n \ge 6$ this is the extremal number $\mathrm{ex}_3(n, \mathcal{F})$ of the family
$\mathcal{F}$ of $3$-uniform hypergraphs with $6$ vertices and $3$ edges, since a set of triples
contains a member of $\mathcal{F}$ exactly when some $6$ points carry $3$ of the triples. -/
noncomputable def sixThreeExtremalNumber (n : ℕ) : ℕ :=
  sSup {e | ∃ E : Finset (Finset (Fin n)), (∀ t ∈ E, t.card = 3) ∧
    (∀ S : Finset (Fin n), S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2) ∧ E.card = e}

/-- **The Brown–Erdős–Sós (6, 3) conjecture.** For $n \in \mathbb{N}$ let $\mathrm{ex}_3(n)$ be
the largest number of $3$-element subsets of $\{1, \dots, n\}$ such that every set of at most $6$
of these points contains at most $2$ of the chosen subsets. The conjecture (Erdős Problem 716) is
the proposition that $\mathrm{ex}_3(n) / n^2 \to 0$ as $n \to \infty$, that is,
$\mathrm{ex}_3(n) = o(n^2)$. -/
def sixThreeExtremalNumberLittleO : Prop :=
  Tendsto (fun n : ℕ => (sixThreeExtremalNumber n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0)

open Finset SimpleGraph

variable {V : Type*} {E : Finset (Finset V)}

/-- The graph whose edges are the pairs occurring in the family of triples. -/
private def shadowGraph (E : Finset (Finset V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ T ∈ E, x ∈ T ∧ y ∈ T
  symm := ⟨fun _ _ ⟨hne, T, hT, hx, hy⟩ ↦ ⟨hne.symm, T, hT, hy, hx⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

private lemma shadowGraph_is3Clique
    (h3 : ∀ T ∈ E, T.card = 3) {T : Finset V} (hT : T ∈ E) :
    (shadowGraph E).IsNClique 3 T := by
  refine ⟨?_, h3 T hT⟩
  intro x hx y hy hxy
  exact ⟨hxy, T, hT, hx, hy⟩

variable [DecidableEq V]

private lemma union_card_add_le {P S T : Finset V} (hS : P ⊆ S) (hT : P ⊆ T) :
    (S ∪ T).card + P.card ≤ S.card + T.card := by
  rw [← card_union_add_card_inter S T]
  exact Nat.add_le_add_left (card_le_card (subset_inter hS hT)) _

private lemma no_three_triples
    (hfree : ∀ S : Finset V, S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2)
    {A B C : Finset V} (hA : A ∈ E) (hB : B ∈ E) (hC : C ∈ E)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hcard : (A ∪ B ∪ C).card ≤ 6) :
    False := by
  refine (hfree _ hcard).not_gt (two_lt_card_iff.mpr ⟨A, B, C, ?_, ?_, ?_, hAB, hAC, hBC⟩)
  · exact mem_filter.mpr ⟨hA, subset_union_left.trans subset_union_left⟩
  · exact mem_filter.mpr ⟨hB, subset_union_right.trans subset_union_left⟩
  · exact mem_filter.mpr ⟨hC, subset_union_right⟩

private lemma card_triples_containing_edge_le_two
    (h3 : ∀ T ∈ E, T.card = 3)
    (hfree : ∀ S : Finset V, S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2)
    {e : Sym2 V} (he : ¬ e.IsDiag) : (E.filter (fun T ↦ e ∈ T.sym2)).card ≤ 2 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy := Sym2.mk_isDiag_iff.not.mp he
    have hp : ({x, y} : Finset V).card = 2 := card_pair hxy
    by_contra! h
    obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ := two_lt_card_iff.mp h
    simp only [mem_filter, mk_mem_sym2_iff, ← singleton_subset_iff (a := y),
      ← insert_subset_iff] at hA hB hC
    have h₁ := union_card_add_le hA.2 hB.2
    have h₂ := union_card_add_le (hA.2.trans (subset_union_left (s₂ := B))) hC.2
    rw [hp, h3 A hA.1, h3 B hB.1] at h₁
    rw [hp, h3 C hC.1] at h₂
    exact no_three_triples hfree hA.1 hB.1 hC.1 hAB hAC hBC (by omega)

-- A triangle outside the original family would have three distinct witnessing triples.
-- The witnesses share vertices along the triangle, so their union has size at most six.
private lemma shadowGraph_cliqueFinset [Fintype V] [DecidableRel (shadowGraph E).Adj]
    (h3 : ∀ T ∈ E, T.card = 3)
    (hfree : ∀ S : Finset V, S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2) :
    (shadowGraph E).cliqueFinset 3 = E := by
  ext T
  rw [mem_cliqueFinset_iff]
  refine ⟨?_, shadowGraph_is3Clique h3⟩
  intro hT
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp hT
  by_contra hnot
  have hno (A : Finset V) (hA : A ∈ E) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) : False := by
    have hsub : {x, y, z} ⊆ A :=
      insert_subset_iff.mpr ⟨hx, insert_subset_iff.mpr ⟨hy, singleton_subset_iff.mpr hz⟩⟩
    exact hnot (eq_of_subset_of_card_le hsub (by rw [h3 A hA, hT.card_eq]) ▸ hA)
  obtain ⟨A, hA, hxA, hyA⟩ := hxy.2
  obtain ⟨B, hB, hxB, hzB⟩ := hxz.2
  obtain ⟨C, hC, hyC, hzC⟩ := hyz.2
  have hAB : A ≠ B := by
    rintro rfl
    exact hno A hA hxA hyA hzB
  have hAC : A ≠ C := by
    rintro rfl
    exact hno A hA hxA hyA hzC
  have hBC : B ≠ C := by
    rintro rfl
    exact hno B hB hxB hyC hzB
  have h₁ := union_card_add_le (singleton_subset_iff.mpr hxA) (singleton_subset_iff.mpr hxB)
  have h₂ := union_card_add_le
    (insert_subset_iff.mpr ⟨mem_union_left B hyA, singleton_subset_iff.mpr (mem_union_right A hzB)⟩)
    (insert_subset_iff.mpr ⟨hyC, singleton_subset_iff.mpr hzC⟩)
  rw [card_singleton, h3 A hA, h3 B hB] at h₁
  rw [card_pair hyz.1, h3 C hC] at h₂
  exact no_three_triples hfree hA hB hC hAB hAC hBC (by omega)

-- Each original triple loses at least one edge, and each lost edge hits at most two triples.
private lemma card_le_twice_removed_edges [Fintype V] [DecidableRel (shadowGraph E).Adj]
    (h3 : ∀ T ∈ E, T.card = 3)
    (hfree : ∀ S : Finset V, S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2)
    {H : SimpleGraph V} [DecidableRel H.Adj] (hH : H.CliqueFree 3) :
    E.card ≤ ((shadowGraph E).edgeFinset \ H.edgeFinset).card * 2 := by
  rw [← Nat.mul_one E.card]
  refine card_mul_le_card_mul (fun T e ↦ e ∈ Finset.sym2 T) ?_ ?_
  · intro T hT
    apply card_pos.mpr
    have htriangle := shadowGraph_is3Clique h3 hT
    have hmissing : ¬ H.IsClique (T : Set V) :=
      fun hclique ↦ hH T ⟨hclique, h3 T hT⟩
    obtain ⟨x, y, hxy, hnot⟩ := H.not_isClique_iff.mp hmissing
    refine ⟨s(x.val, y.val), ?_⟩
    rw [mem_bipartiteAbove]
    refine ⟨?_, mk_mem_sym2_iff.mpr ⟨x.property, y.property⟩⟩
    refine Finset.mem_sdiff.mpr ⟨?_, fun he ↦ hnot (mem_edgeFinset.mp he)⟩
    exact mem_edgeFinset.mpr
      (htriangle.isClique x.property y.property (Subtype.val_injective.ne hxy))
  · intro e he
    exact card_triples_containing_edge_le_two h3 hfree
      ((shadowGraph E).not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_sdiff.mp he).1))

private lemma exists_maximizing_family (n : ℕ) :
    ∃ E : Finset (Finset (Fin n)), (∀ T ∈ E, T.card = 3) ∧
      (∀ S : Finset (Fin n), S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2) ∧
      E.card = sixThreeExtremalNumber n := by
  let S : Set ℕ := {e | ∃ E : Finset (Finset (Fin n)), (∀ T ∈ E, T.card = 3) ∧
    (∀ S : Finset (Fin n), S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2) ∧ E.card = e}
  change sSup S ∈ S
  apply Nat.sSup_mem
  · exact ⟨0, ∅, by simp⟩
  · refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
    rintro e ⟨E, _, _, rfl⟩
    exact card_le_univ E

/-- **The Ruzsa–Szemerédi (6, 3) theorem.** For $n \in \mathbb{N}$ let $\mathrm{ex}_3(n)$ be the
largest number of $3$-element subsets of $\{1, \dots, n\}$ such that every set of at most $6$ of
these points contains at most $2$ of the chosen subsets. Then $\mathrm{ex}_3(n) / n^2 \to 0$ as
$n \to \infty$, that is, $\mathrm{ex}_3(n) = o(n^2)$.

Source: T. F. Bloom, Erdős Problems, Problem #716,
https://www.erdosproblems.com/716 (status PROVED (LEAN)); resolution: I. Z. Ruzsa and E. Szemerédi,
Triple systems with no six points carrying three triangles, Combinatorics (Proc. Fifth Hungarian
Colloq., Keszthely, 1976), Vol. II (1978), 939-945, erdosproblems.com/716: 'The answer is yes,
proved by Ruzsa and Szemerédi' (the Ruzsa-Szemerédi problem), https://www.erdosproblems.com/716.
-/
theorem sixThreeExtremalNumberLittleO_holds : sixThreeExtremalNumberLittleO := by
  classical
  rw [sixThreeExtremalNumberLittleO, Metric.tendsto_atTop']
  intro ε hε
  let δ := triangleRemovalBound (ε / 2)
  have hδ : 0 < δ := triangleRemovalBound_pos (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hquad : (2 : ℝ) < δ * n := by
    have hlarge : 2 / δ < (n : ℝ) := hN.trans (Nat.cast_lt.mpr hn)
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hlarge
  obtain ⟨E, h3, hfree, hcard⟩ := exists_maximizing_family n
  let G := shadowGraph E
  have htri : G.cliqueFinset 3 = E := shadowGraph_cliqueFinset h3 hfree
  have hE : E.card ≤ n ^ 2 * 2 := by
    have hbot := card_le_twice_removed_edges h3 hfree
      (H := (⊥ : SimpleGraph (Fin n))) (cliqueFree_bot (by decide))
    calc
      E.card ≤ G.edgeFinset.card * 2 :=
        hbot.trans (Nat.mul_le_mul_right 2 (card_le_card sdiff_subset))
      _ ≤ n ^ 2 * 2 := by
        apply Nat.mul_le_mul_right
        simpa using G.card_edgeFinset_le_card_choose_two.trans
          (Nat.choose_le_pow (Fintype.card (Fin n)) 2)
  have hsmall : ((G.cliqueFinset 3).card : ℝ) < δ * (Fintype.card (Fin n) : ℝ) ^ 3 := by
    rw [htri, Fintype.card_fin]
    calc
      (E.card : ℝ) ≤ (n : ℝ) ^ 2 * 2 := by exact_mod_cast hE
      _ < (n : ℝ) ^ 2 * (δ * n) := mul_lt_mul_of_pos_left hquad (sq_pos_of_pos hn_pos)
      _ = δ * (n : ℝ) ^ 3 := by ring
  obtain ⟨H, hHG, hDec, hrem, hH⟩ := triangle_removal (ε := ε / 2) hsmall
  have hremoved := card_le_twice_removed_edges h3 hfree hH
  rw [card_sdiff_of_subset (edgeFinset_mono hHG)] at hremoved
  rw [← hcard, Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)]
  calc
    (E.card : ℝ) ≤ ((G.edgeFinset.card - H.edgeFinset.card : ℕ) : ℝ) * 2 := by
      exact_mod_cast hremoved
    _ = (G.edgeFinset.card - H.edgeFinset.card) * 2 := by
      rw [Nat.cast_sub (card_le_card (edgeFinset_mono hHG))]
    _ < ε * (n : ℝ) ^ 2 := by
      rw [Fintype.card_fin] at hrem
      push_cast at hrem
      linarith only [hrem]

end MathlibExt.Combinatorics.SixPointsThreeTriplesErdosProblem716Wanted
