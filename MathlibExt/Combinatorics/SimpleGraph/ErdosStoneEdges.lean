/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Erdős–Stone theorem, edge form

Every graph on `n` vertices with at least `(1 - 1/r + ε) n² / 2` edges contains `K_{r+1}(t)` once
`n` is large. The proof reduces to Mathlib's minimum-degree form
`SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree` by deleting vertices of
small degree: while some vertex of the current vertex set `S` has fewer than `β |S|` neighbours in
`S` (with `β = 1 - 1/r + ε/2`), delete it. The quantity
`Φ(S) = (ordered adjacent pairs in S) - β |S| (|S| + 1)` increases at every deletion, and starts at
about `ε n² / 2`; since `Φ(S) ≤ |S|²`, the process stops at a set of at least about `√(ε/2) n`
vertices, which induces a graph of minimum degree at least `β |S|`. This is the deletion argument
of Lemma 3.3.12 of the *Extremal Combinatorics* lecture notes (extremalcombinatorics.com),
with a potential function in place of the explicit count.

References: P. Erdős and A. H. Stone, *Bull. Amer. Math. Soc.* 52 (1946), in the form of the
introduction of B. Bollobás, P. Erdős and M. Simonovits, "On the structure of edge graphs II",
*J. London Math. Soc. (2)* 12 (1976); *Extremal Combinatorics* lecture notes
(extremalcombinatorics.com), Section 3.3.
-/

@[expose] public section

open Filter Finset SimpleGraph

namespace MathlibExt.Combinatorics.SimpleGraph.ErdosStoneEdges

variable {n : ℕ} (G : _root_.SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **Degree inside a vertex set.** The number of neighbours of `v` in `S`. -/
def degIn (S : Finset (Fin n)) (v : Fin n) : ℕ := #(S.filter (G.Adj v))

/-- **Ordered adjacent pairs inside a vertex set.** `∑_{v ∈ S} deg_S(v)`, twice the number of edges
of the subgraph induced by `S`. -/
def adjPairsIn (S : Finset (Fin n)) : ℕ := ∑ v ∈ S, degIn G S v

lemma degIn_le_card (S : Finset (Fin n)) (v : Fin n) : degIn G S v ≤ #S :=
  card_filter_le _ _

lemma adjPairsIn_le_sq (S : Finset (Fin n)) : adjPairsIn G S ≤ #S ^ 2 := by
  unfold adjPairsIn
  calc ∑ v ∈ S, degIn G S v ≤ ∑ _v ∈ S, #S := sum_le_sum fun v _ => degIn_le_card G S v
    _ = #S ^ 2 := by rw [sum_const, smul_eq_mul, sq]

lemma adjPairsIn_univ : adjPairsIn G univ = 2 * #G.edgeFinset := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  refine sum_congr rfl fun v _ => ?_
  rw [degIn, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

lemma degIn_erase (S : Finset (Fin n)) {v : Fin n} (u : Fin n) :
    (degIn G (S.erase v) u : ℝ) = degIn G S u - if v ∈ S ∧ G.Adj u v then 1 else 0 := by
  unfold degIn
  rw [filter_erase]
  split_ifs with h
  · rw [card_erase_of_mem (mem_filter.2 h), Nat.cast_sub (card_pos.2 ⟨v, mem_filter.2 h⟩),
      Nat.cast_one]
  · rw [erase_eq_of_notMem (fun hm => h (mem_filter.1 hm)), sub_zero]

lemma adjPairsIn_erase (S : Finset (Fin n)) {v : Fin n} (hv : v ∈ S) :
    (adjPairsIn G (S.erase v) : ℝ) = adjPairsIn G S - 2 * degIn G S v := by
  unfold adjPairsIn
  push_cast
  rw [sum_congr rfl fun u _ => degIn_erase G S u, sum_sub_distrib]
  have h1 : ∑ u ∈ S.erase v, (degIn G S u : ℝ) = ∑ u ∈ S, (degIn G S u : ℝ) - degIn G S v := by
    rw [← add_sum_erase S _ hv]; ring
  have h2 : ∑ u ∈ S.erase v, (if v ∈ S ∧ G.Adj u v then (1 : ℝ) else 0) = degIn G S v := by
    rw [sum_boole]
    unfold degIn
    congr 2
    ext u
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hu⟩, _, huv⟩
      exact ⟨hu, huv.symm⟩
    · rintro ⟨hu, hvu⟩
      exact ⟨⟨hvu.ne.symm, hu⟩, hv, hvu.symm⟩
  rw [h1, h2]
  ring

/-- **Deletion of low-degree vertices.** For every `β` and `Φ₀`, a vertex set `S` with
`adjPairsIn S - β |S| (|S| + 1) ≥ Φ₀` contains a set `T` with the same property on which every
vertex has at least `β |T|` neighbours in `T` (*Extremal Combinatorics* lecture notes,
extremalcombinatorics.com, Lemma 3.3.12, with a potential function). -/
theorem exists_subset_forall_le_degIn (β Φ₀ : ℝ) (S : Finset (Fin n))
    (hS : Φ₀ ≤ adjPairsIn G S - β * #S * (#S + 1)) :
    ∃ T ⊆ S, Φ₀ ≤ adjPairsIn G T - β * #T * (#T + 1) ∧ ∀ v ∈ T, β * #T ≤ degIn G T v := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hall : ∀ v ∈ S, β * #S ≤ degIn G S v
    · exact ⟨S, subset_refl S, hS, hall⟩
    push Not at hall
    obtain ⟨v, hv, hlt⟩ := hall
    have hcard : ((#(S.erase v) : ℕ) : ℝ) = #S - 1 := by
      rw [card_erase_of_mem hv, Nat.cast_sub (card_pos.2 ⟨v, hv⟩), Nat.cast_one]
    have hΦ : Φ₀ ≤ adjPairsIn G (S.erase v) - β * #(S.erase v) * (#(S.erase v) + 1) := by
      rw [adjPairsIn_erase G S hv, hcard]
      nlinarith
    obtain ⟨T, hT, hΦT, hdeg⟩ := ih (S.erase v) (erase_ssubset hv) hΦ
    exact ⟨T, hT.trans (erase_subset v S), hΦT, hdeg⟩

lemma degree_comap_orderEmbOfFin (T : Finset (Fin n))
    [DecidableRel (G.comap (T.orderEmbOfFin rfl).toEmbedding).Adj] (i : Fin #T) :
    (G.comap (T.orderEmbOfFin rfl).toEmbedding).degree i =
      degIn G T (T.orderEmbOfFin rfl i) := by
  rw [← _root_.SimpleGraph.card_neighborFinset_eq_degree,
    _root_.SimpleGraph.neighborFinset_eq_filter, degIn,
    ← card_map (T.orderEmbOfFin rfl).toEmbedding]
  congr 1
  ext u
  simp only [Finset.mem_map, mem_filter, mem_univ, true_and, _root_.SimpleGraph.comap_adj]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨orderEmbOfFin_mem T rfl j, hj⟩
  · rintro ⟨hu, hadj⟩
    have hu' : u ∈ Set.range (T.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hu
    obtain ⟨j, rfl⟩ := hu'
    exact ⟨j, hadj, rfl⟩

/-- **Erdős–Stone theorem.** For every `r ≥ 1`, `t` and `ε > 0`, every simple graph on `n`
vertices with at least `(1 - 1/r + ε) n² / 2` edges contains the complete `(r + 1)`-partite graph
`K_{r+1}(t)` with parts of size `t`, once `n` is large enough (Erdős and Stone, 1946; in the form
"`m ≥ ((d - 2)/(2(d - 1)) + c) n²` forces `K_d(t)`" of the introduction of Bollobás, Erdős and
Simonovits, *J. London Math. Soc. (2)* 12 (1976), with `d = r + 1` and `c = ε / 2`). Proved from
Mathlib's minimum-degree form
`SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree` by the deletion argument
of Lemma 3.3.12 of the *Extremal Combinatorics* lecture notes (extremalcombinatorics.com). -/
theorem eventually_completeEquipartiteGraph_isContained_of_card_edgeFinset
    {r : ℕ} (hr : 1 ≤ r) (t : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {G : _root_.SimpleGraph (Fin n)} [DecidableRel G.Adj],
      (#G.edgeFinset : ℝ) ≥ (1 - 1 / r + ε) * n ^ 2 / 2 →
        _root_.SimpleGraph.completeEquipartiteGraph (r + 1) t ⊑ G := by
  classical
  set β : ℝ := 1 - 1 / r + ε / 2 with hβ
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hβ0 : 0 ≤ β := by
    have : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hr'
    linarith
  obtain ⟨N', hN'⟩ := eventually_atTop.mp
    (_root_.SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree
      (half_pos hε) r t)
  set M : ℕ := max N' 1 with hM
  set K : ℝ := (M : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [eventually_ge_atTop ⌈2 * (β + K) / ε⌉₊, eventually_ge_atTop 1] with n hn hn1
  intro G _ hG
  have hnR : 2 * (β + K) / ε ≤ n := Nat.ceil_le.1 hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set Φ₀ : ℝ := adjPairsIn G univ - β * #(univ : Finset (Fin n)) *
    (#(univ : Finset (Fin n)) + 1) with hΦ₀def
  obtain ⟨T, -, hΦT, hdeg⟩ := exists_subset_forall_le_degIn G β Φ₀ univ le_rfl
  have hcardU : (#(univ : Finset (Fin n)) : ℝ) = n := by simp
  have hΦ₀ : K ≤ Φ₀ := by
    rw [hΦ₀def, hcardU, adjPairsIn_univ]
    push_cast
    have h1 : K ≤ ε / 2 * n - β := by
      have := (div_le_iff₀ hε).1 hnR
      linarith
    have h2 : K ≤ (ε / 2 * n - β) * n := by nlinarith
    nlinarith
  have hT2 : K ≤ (#T : ℝ) ^ 2 := by
    have h' : (adjPairsIn G T : ℝ) ≤ (#T : ℝ) ^ 2 := by exact_mod_cast adjPairsIn_le_sq G T
    have : 0 ≤ β * #T * (#T + 1) := by positivity
    linarith
  have hMT : M ≤ #T := by
    have h : M ^ 2 ≤ #T ^ 2 := by rw [hK] at hT2; exact_mod_cast hT2
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h
  have hTpos : 0 < #T := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right N' 1)) hMT
  have : Nonempty (Fin #T) := ⟨⟨0, hTpos⟩⟩
  set f := (T.orderEmbOfFin rfl).toEmbedding with hf
  have hmin : ((G.comap f).minDegree : ℝ) ≥ (1 - 1 / r + ε / 2) * (#T : ℕ) := by
    have hk : ⌈β * #T⌉₊ ≤ (G.comap f).minDegree := by
      refine _root_.SimpleGraph.le_minDegree_of_forall_le_degree _ _ fun i => ?_
      rw [degree_comap_orderEmbOfFin]
      exact Nat.ceil_le.2 (hdeg _ (orderEmbOfFin_mem T rfl i))
    calc (1 - 1 / r + ε / 2) * ((#T : ℕ) : ℝ) = β * #T := by rw [hβ]
      _ ≤ ⌈β * #T⌉₊ := Nat.le_ceil _
      _ ≤ (G.comap f).minDegree := by exact_mod_cast hk
  exact (hN' #T (le_trans (le_max_left _ _) hMT) hmin).trans
    (_root_.SimpleGraph.Embedding.comap f G).isContained

end MathlibExt.Combinatorics.SimpleGraph.ErdosStoneEdges
