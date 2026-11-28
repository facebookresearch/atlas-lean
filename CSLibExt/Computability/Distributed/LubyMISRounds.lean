/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.LubyMIS
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Log
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.UniformOn

/-!
# Luby's maximal independent set algorithm

Luby's algorithm computes a maximal independent set of a graph `G` on `Fin n` in rounds. In each
round every remaining vertex draws a random value; the remaining vertices whose value is smaller
than that of every remaining neighbor join the independent set (the selection step
`lubySelect`), and they and their neighbors are removed. A remaining vertex with no remaining
neighbor is always selected.

Here a round is run for given priorities `prio : Fin n → ℕ`, with ties broken by vertex index as
in `lubySelect`. In the probabilistic statements the values of a round are those of a uniformly
random permutation `σ` of the vertices, vertex `v` getting the value `σ v`, so no two vertices tie;
independent uniform values in `[0, 1]` are almost surely distinct, and their order is then a
uniformly random order of the remaining vertices. The rounds use independent permutations: the
product `Measure.pi` of uniform measures `uniformOn Set.univ` on `Equiv.Perm (Fin n)`.

## Main definitions

* `lubyRemaining`: the vertices left after one round.
* `lubyRound`: one round, on the pair of the independent set built so far and the remaining
  vertices.
* `lubyRun`: the algorithm, run for a list of priority functions, one per round.
* `remainingEdges`: the edges of `G` with both endpoints in a given set.

## Main results

* `lubyRun_maximal`: for any priorities, once no vertex remains the output is a maximal
  independent set and later rounds change nothing, and after `n` rounds no vertex remains.
* `inv_le_uniformOn_smallest`: the key estimate: for an edge `uv` with `u` remaining, `u` has
  the smallest value among the remaining neighbors of `u` and of `v` with probability at least
  `1 / (d(u) + d(v))`, the degrees taken among the remaining vertices.
* `expected_removed_edges_ge`: in a round, the expected number of removed edges is at least half
  the number of remaining edges.
* `prob_lubyRun_nonempty_le`: some vertex remains after `T + 1` rounds with probability at most
  `|E| / 2 ^ T`.
* `prob_lubyRun_nonempty_le_inv_pow`: some vertex remains after `(c + 2) ⌈log₂ n⌉ + 1` rounds
  with probability at most `1 / n ^ c`.
* `luby_mis`: all of the above, except the key estimate, in one statement.

The proof of the expectation bound follows Luby's argument: when `u` has the smallest value among
the remaining neighbors of `u` and of `v`, the vertex `u` is selected and all edges at `v` are
removed, and for a fixed `v` these events are disjoint. The bound on the rounds follows by
induction on the number of rounds: the expected number of remaining edges at least halves in
each round, and a round that starts with no remaining edge removes every remaining vertex.

## References

* M. Luby, *A simple parallel algorithm for the maximal independent set problem*, SIAM
  Journal on Computing 15(4), 1986.
* G. Miller, *Luby's Algorithm for Maximal Independent Set*, lecture notes for 15-451/651,
  Carnegie Mellon University, 2019, Sections 3.2 and 3.3.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal Nat

namespace Cslib.Distributed.LubyMIS

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **Vertices left after a round of Luby's algorithm.** Let $G$ be a graph on
$\{0, \dots, n-1\}$, let $\pi$ assign a priority in $\mathbb{N}$ to each vertex and let $R$ be the
set of remaining vertices. The vertices left after the round are those of $R$ that are neither
selected by the selection step of Luby's algorithm (the vertices of $R$ whose priority is smaller
than that of every neighbor in $R$, ties broken by vertex index) nor adjacent to a selected
vertex. -/
def lubyRemaining (prio : Fin n → ℕ) (R : Finset (Fin n)) : Finset (Fin n) :=
  R.filter fun v => v ∉ lubySelect G prio R ∧ ∀ u ∈ lubySelect G prio R, ¬ G.Adj u v

/-- **A round of Luby's algorithm.** Let $G$ be a graph on $\{0, \dots, n-1\}$ and let $\pi$
assign a priority in $\mathbb{N}$ to each vertex. A round takes a pair $(I, R)$ of the
independent set built so far and the set of remaining vertices to $(I \cup S, R')$, where $S$ is
the set of vertices of $R$ whose priority is smaller than that of every neighbor in $R$, ties
broken by vertex index (in particular every vertex of $R$ with no neighbor in $R$ is in $S$), and
$R'$ is the set of vertices of $R$ that are neither in $S$ nor adjacent to a vertex of $S$. -/
def lubyRound (s : Finset (Fin n) × Finset (Fin n)) (prio : Fin n → ℕ) :
    Finset (Fin n) × Finset (Fin n) :=
  (s.1 ∪ lubySelect G prio s.2, lubyRemaining G prio s.2)

/-- **Running Luby's algorithm.** Let $G$ be a graph on $\{0, \dots, n-1\}$ and
let $\pi_1, \dots, \pi_k$ be priority functions on its vertices. The algorithm starts from the
empty independent set and all vertices remaining, and runs one round of Luby's algorithm with the
priorities $\pi_t$ for each $t = 1, \dots, k$ in turn: the remaining vertices whose priority is
smaller than that of every remaining neighbor, ties broken by vertex index, join the independent
set, and they and their neighbors are removed. The result is the pair of the independent set
built and the set of vertices still remaining. -/
def lubyRun (prios : List (Fin n → ℕ)) : Finset (Fin n) × Finset (Fin n) :=
  prios.foldl (lubyRound G) (∅, univ)

/-- **Edges among a set of vertices.** For a graph $G$ on $\{0, \dots, n-1\}$ and a set $R$ of
vertices, the edges of $G$ with both endpoints in $R$, that is, the edges of the subgraph of $G$
induced by $R$. -/
def remainingEdges (R : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ R

/-! ### The output is a maximal independent set -/

/- The invariant of the algorithm: `s.1` is independent and disjoint from `s.2`, every removed
vertex is in `s.1` or adjacent to a vertex of `s.1`, and no remaining vertex is adjacent to a
vertex of `s.1`. -/
private structure RoundInvariant (s : Finset (Fin n) × Finset (Fin n)) : Prop where
  indep : G.IsIndepSet (s.1 : Set (Fin n))
  disj : Disjoint s.1 s.2
  covered : ∀ v, v ∉ s.2 → v ∈ s.1 ∨ ∃ u ∈ s.1, G.Adj u v
  free : ∀ v ∈ s.2, ∀ u ∈ s.1, ¬ G.Adj u v

omit [DecidableRel G.Adj] in
private theorem inv_init : RoundInvariant G (∅, univ) where
  indep := by simp
  disj := by simp
  covered v hv := absurd (mem_univ v) hv
  free := by simp

private theorem inv_round {s : Finset (Fin n) × Finset (Fin n)}
    (h : RoundInvariant G s) (prio : Fin n → ℕ) : RoundInvariant G (lubyRound G s prio) := by
  obtain ⟨I, R⟩ := s
  have hSR : lubySelect G prio R ⊆ R := lubySelect_subset G prio R
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [lubyRound, coe_union]
    intro x hx y hy hxy hadj
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact h.indep hx hy hxy hadj
    · exact h.free y (hSR hy) x hx hadj
    · exact h.free x (hSR hx) y hy hadj.symm
    · exact lubySelect_isIndepSet G prio R hx hy hxy hadj
  · simp only [lubyRound, lubyRemaining]
    refine disjoint_left.2 fun v hv hv' => ?_
    rw [mem_filter] at hv'
    rcases mem_union.1 hv with hv | hv
    · exact disjoint_left.1 h.disj hv hv'.1
    · exact hv'.2.1 hv
  · intro v hv
    simp only [lubyRound, lubyRemaining, mem_filter, not_and_or, not_forall, not_not] at hv ⊢
    rcases hv with hv | hv | ⟨u, hu, hadj⟩
    · rcases h.covered v hv with hvI | ⟨u, hu, hadj⟩
      · exact Or.inl (mem_union_left _ hvI)
      · exact Or.inr ⟨u, mem_union_left _ hu, hadj⟩
    · exact Or.inl (mem_union_right _ hv)
    · exact Or.inr ⟨u, mem_union_right _ hu, hadj⟩
  · intro v hv u hu
    simp only [lubyRound, lubyRemaining, mem_filter] at hv hu
    rcases mem_union.1 hu with hu | hu
    · exact h.free v hv.1 u hu
    · exact hv.2.2 u hu

private theorem inv_foldl (l : List (Fin n → ℕ)) {s : Finset (Fin n) × Finset (Fin n)}
    (h : RoundInvariant G s) : RoundInvariant G (l.foldl (lubyRound G) s) := by
  induction l generalizing s with
  | nil => exact h
  | cons p l ih => exact ih (inv_round G h p)

omit [DecidableRel G.Adj] in
private theorem maximal_of_inv {s : Finset (Fin n) × Finset (Fin n)}
    (h : RoundInvariant G s) (hR : s.2 = ∅) : Maximal G.IsIndepSet (s.1 : Set (Fin n)) := by
  refine ⟨h.indep, fun t ht hst x hx => ?_⟩
  by_contra hxI
  rcases h.covered x (by simp [hR]) with h' | ⟨u, hu, hadj⟩
  · exact hxI h'
  · exact ht (hst hu) hx (G.ne_of_adj hadj) hadj

private theorem lubyKey_injective (prio : Fin n → ℕ) : Function.Injective (lubyKey prio) := by
  intro v u h
  by_contra hne
  rcases lt_trichotomy (prio v) (prio u) with h1 | h1 | h1
  · exact ((lubyKey_lt_iff prio v u).2 (Or.inl h1)).ne h
  · rcases lt_or_gt_of_ne hne with h2 | h2
    · exact ((lubyKey_lt_iff prio v u).2 (Or.inr ⟨h1, h2⟩)).ne h
    · exact ((lubyKey_lt_iff prio u v).2 (Or.inr ⟨h1.symm, h2⟩)).ne h.symm
  · exact ((lubyKey_lt_iff prio u v).2 (Or.inl h1)).ne h.symm

/- A nonempty set of remaining vertices has a selected vertex: one of least key. -/
private theorem exists_mem_lubySelect (prio : Fin n → ℕ) {R : Finset (Fin n)}
    (hR : R.Nonempty) : ∃ v ∈ R, v ∈ lubySelect G prio R := by
  obtain ⟨v, hv, hmin⟩ := R.exists_min_image (lubyKey prio) hR
  refine ⟨v, hv, mem_filter.2 ⟨hv, fun u hu => ?_⟩⟩
  rw [mem_inter, SimpleGraph.mem_neighborFinset] at hu
  exact lt_of_le_of_ne (hmin u hu.2) fun h => G.ne_of_adj hu.1 (lubyKey_injective prio h)

private theorem lubyRemaining_subset (prio : Fin n → ℕ) (R : Finset (Fin n)) :
    lubyRemaining G prio R ⊆ R :=
  filter_subset _ _

private theorem card_lubyRemaining_lt (prio : Fin n → ℕ) {R : Finset (Fin n)}
    (hR : R.Nonempty) : #(lubyRemaining G prio R) < #R := by
  obtain ⟨v, hv, hvS⟩ := exists_mem_lubySelect G prio hR
  refine card_lt_card ⟨lubyRemaining_subset G prio R, fun h => ?_⟩
  exact (mem_filter.1 (h hv)).2.1 hvS

private theorem lubyRemaining_empty (prio : Fin n → ℕ) : lubyRemaining G prio ∅ = ∅ :=
  filter_empty _

private theorem card_foldl_le (l : List (Fin n → ℕ)) (s : Finset (Fin n) × Finset (Fin n)) :
    #(l.foldl (lubyRound G) s).2 ≤ #s.2 - l.length := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, List.length_cons]
    refine (ih _).trans ?_
    rcases s.2.eq_empty_or_nonempty with h | h
    · simp [lubyRound, h, lubyRemaining_empty]
    · have := card_lubyRemaining_lt G p h
      simp only [lubyRound]
      omega

private theorem foldl_of_remaining_empty (l : List (Fin n → ℕ))
    {s : Finset (Fin n) × Finset (Fin n)} (h : s.2 = ∅) : l.foldl (lubyRound G) s = s := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hs : lubyRound G s p = s := by
      obtain ⟨I, R⟩ := s
      simp only at h
      subst h
      simp [lubyRound, lubySelect, lubyRemaining_empty]
    rw [List.foldl_cons, hs, ih]

/- **Luby's algorithm outputs a maximal independent set.** For any priorities: once no vertex
remains, the independent set built is a maximal independent set of `G` and further rounds change
nothing; and after `n` rounds no vertex remains. -/
theorem lubyRun_maximal (prios : List (Fin n → ℕ)) :
    ((lubyRun G prios).2 = ∅ →
        Maximal G.IsIndepSet ((lubyRun G prios).1 : Set (Fin n)) ∧
          ∀ prios' : List (Fin n → ℕ), lubyRun G (prios ++ prios') = lubyRun G prios) ∧
      (n ≤ prios.length → (lubyRun G prios).2 = ∅) := by
  refine ⟨fun h => ⟨maximal_of_inv G (inv_foldl G prios (inv_init G)) h, fun prios' => ?_⟩,
    fun h => ?_⟩
  · rw [lubyRun, List.foldl_append]
    exact foldl_of_remaining_empty G prios' h
  · have := card_foldl_le G prios (∅, univ)
    simp only [card_univ, Fintype.card_fin] at this
    exact card_eq_zero.1 (by rw [lubyRun]; omega)

/-! ### One round with a random permutation -/

/- The graph of the remaining edges: adjacency in `G` between two vertices of `R`. -/
private def remGraph (R : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ∈ R ∧ v ∈ R
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

private instance (R : Finset (Fin n)) : DecidableRel (remGraph G R).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∈ R ∧ v ∈ R))

private theorem edgeFinset_remGraph (R : Finset (Fin n)) :
    (remGraph G R).edgeFinset = remainingEdges G R := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, remainingEdges, mem_filter,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change G.Adj a b ∧ a ∈ R ∧ b ∈ R ↔ _
    constructor
    · rintro ⟨h, ha, hb⟩
      refine ⟨h, fun v hv => ?_⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      exacts [ha, hb]
    · rintro ⟨h, hR⟩
      exact ⟨h, hR a (Sym2.mem_mk_left a b), hR b (Sym2.mem_mk_right a b)⟩

private theorem neighborFinset_inter_eq_filter (R : Finset (Fin n)) (v : Fin n) :
    G.neighborFinset v ∩ R = R.filter (G.Adj v) := by
  ext u
  simp [and_comm]

/- The handshake lemma among the vertices of `R`. -/
private theorem sum_card_neighbor_inter (R : Finset (Fin n)) :
    ∑ v ∈ R, #(G.neighborFinset v ∩ R) = 2 * #(remainingEdges G R) := by
  rw [← edgeFinset_remGraph, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc ∑ v ∈ R, #(G.neighborFinset v ∩ R) = ∑ v ∈ R, (remGraph G R).degree v := by
        refine sum_congr rfl fun v hv => ?_
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        congr 1
        ext u
        simp only [mem_inter, SimpleGraph.mem_neighborFinset]
        change _ ↔ G.Adj v u ∧ v ∈ R ∧ u ∈ R
        tauto
    _ = ∑ v, (remGraph G R).degree v := by
        refine sum_subset (subset_univ R) fun v _ hv => ?_
        rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero]
        ext u
        simp only [SimpleGraph.mem_neighborFinset, notMem_empty, iff_false]
        exact fun h => hv h.2.1

private theorem remainingEdges_mono {R R' : Finset (Fin n)} (h : R' ⊆ R) :
    remainingEdges G R' ⊆ remainingEdges G R :=
  fun _ he => mem_filter.2 ⟨(mem_filter.1 he).1, fun v hv => h ((mem_filter.1 he).2 v hv)⟩

private theorem lubyKey_perm_lt_iff (σ : Equiv.Perm (Fin n)) (v u : Fin n) :
    lubyKey (fun w => (σ w : ℕ)) v < lubyKey (fun w => (σ w : ℕ)) u ↔ σ v < σ u := by
  rw [lubyKey_lt_iff]
  refine ⟨fun h => h.elim id fun h => ?_, Or.inl⟩
  obtain rfl := σ.injective (Fin.ext h.1)
  exact absurd h.2 (lt_irrefl _)

/- The event that `u` has the smallest value among the remaining neighbors of `u` and `v`. -/
private def Smallest (R : Finset (Fin n)) (u v : Fin n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ w ∈ G.neighborFinset u ∩ R ∪ G.neighborFinset v ∩ R, w ≠ u → σ u < σ w

private instance (R : Finset (Fin n)) (u v : Fin n) : DecidablePred (Smallest G R u v) :=
  fun _ => inferInstanceAs (Decidable (∀ _ ∈ _, _))

/- Under a uniformly random permutation, each element of a nonempty set is its smallest element
equally often: the permutations under which `u ∈ S` is the smallest, times `|S|`, are all
`n!` permutations. -/
private theorem card_smallest_mul (S : Finset (Fin n)) {u : Fin n} (hu : u ∈ S) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => ∀ w ∈ S, w ≠ u → σ u < σ w) * #S = n ! := by
  set M : Fin n → Finset (Equiv.Perm (Fin n)) :=
    fun x => univ.filter fun σ => ∀ w ∈ S, w ≠ x → σ x < σ w with hM
  have hmap : ∀ {a b : Fin n}, b ∈ S → ∀ σ ∈ M a, σ * Equiv.swap a b ∈ M b := by
    intro a b hb σ hσ
    simp only [hM, mem_filter, mem_univ, true_and, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.swap_apply_right] at hσ ⊢
    intro w hw hwb
    rcases eq_or_ne w a with rfl | hwa
    · rw [Equiv.swap_apply_left]
      exact hσ b hb (Ne.symm hwb)
    · rw [Equiv.swap_apply_of_ne_of_ne hwa hwb]
      exact hσ w hw hwa
  have hcard : ∀ x ∈ S, #(M x) = #(M u) := by
    intro x hx
    refine card_nbij' (· * Equiv.swap x u) (· * Equiv.swap x u) (fun σ hσ => hmap hu σ hσ)
      (fun σ hσ => ?_) (fun σ _ => by simp [mul_assoc]) (fun σ _ => by simp [mul_assoc])
    have := hmap hx σ hσ
    rwa [Equiv.swap_comm] at this
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (M x) (M y) := by
    intro x hx y hy hxy
    refine disjoint_left.2 fun σ h1 h2 => ?_
    simp only [hM, mem_filter, mem_univ, true_and] at h1 h2
    exact lt_asymm (h1 y hy (Ne.symm hxy)) (h2 x hx hxy)
  have hcover : S.biUnion M = univ := by
    refine eq_univ_of_forall fun σ => ?_
    obtain ⟨x, hx, hmin⟩ := S.exists_min_image σ ⟨u, hu⟩
    refine mem_biUnion.2 ⟨x, hx, ?_⟩
    simp only [hM, mem_filter, mem_univ, true_and]
    exact fun w hw hwx => lt_of_le_of_ne (hmin w hw) (σ.injective.ne (Ne.symm hwx))
  calc #(M u) * #S = ∑ x ∈ S, #(M x) := by
        rw [sum_congr rfl hcard, sum_const, smul_eq_mul, mul_comm]
    _ = #(S.biUnion M) := (card_biUnion hdisj).symm
    _ = n ! := by rw [hcover, card_univ, Fintype.card_perm, Fintype.card_fin]

private theorem card_smallest_mul_ge {R : Finset (Fin n)} {u v : Fin n} (hu : u ∈ R)
    (huv : G.Adj u v) :
    n ! ≤ #(univ.filter (Smallest G R u v)) *
      (#(G.neighborFinset u ∩ R) + #(G.neighborFinset v ∩ R)) := by
  have hmem : u ∈ G.neighborFinset u ∩ R ∪ G.neighborFinset v ∩ R :=
    mem_union_right _ (mem_inter.2 ⟨(G.mem_neighborFinset v u).2 huv.symm, hu⟩)
  rw [← card_smallest_mul _ hmem]
  exact Nat.mul_le_mul_left _ (card_union_le _ _)

/- When `u` has the smallest value among the remaining neighbors of `u` and `v`, the vertex `u`
is selected, so `v` is removed. -/
private theorem smallest_selected {R : Finset (Fin n)} {u v : Fin n} {σ : Equiv.Perm (Fin n)}
    (hu : u ∈ R) (h : Smallest G R u v σ) : u ∈ lubySelect G (fun w => (σ w : ℕ)) R := by
  refine mem_filter.2 ⟨hu, fun w hw => ?_⟩
  rw [lubyKey_perm_lt_iff]
  exact h w (mem_union_left _ hw)
    (G.ne_of_adj ((G.mem_neighborFinset u w).1 (mem_inter.1 hw).1)).symm

private theorem not_mem_lubyRemaining_of_smallest {R : Finset (Fin n)} {u v : Fin n}
    {σ : Equiv.Perm (Fin n)} (hu : u ∈ R) (huv : G.Adj u v) (h : Smallest G R u v σ) :
    v ∉ lubyRemaining G (fun w => (σ w : ℕ)) R := fun hv =>
  (mem_filter.1 hv).2.2 u (smallest_selected G hu h) huv

/- For a fixed `v`, at most one remaining neighbor `u` of `v` has the smallest value among the
remaining neighbors of `u` and `v`. -/
private theorem card_filter_smallest_le_one (R : Finset (Fin n)) (v : Fin n)
    (σ : Equiv.Perm (Fin n)) :
    #((G.neighborFinset v ∩ R).filter fun u => Smallest G R u v σ) ≤ 1 := by
  refine card_le_one.2 fun a ha b hb => ?_
  by_contra hab
  rw [mem_filter] at ha hb
  exact lt_asymm (ha.2 b (mem_union_right _ hb.1) (Ne.symm hab))
    (hb.2 a (mem_union_right _ ha.1) hab)

/- The removed edges at a remaining vertex `v`, counted with the indicator of some neighbor
having the smallest value, are at most the removed edges at `v`. -/
private theorem card_mul_filter_smallest_le (R : Finset (Fin n)) {v : Fin n} (hv : v ∈ R)
    (σ : Equiv.Perm (Fin n)) :
    #(G.neighborFinset v ∩ R) * #((G.neighborFinset v ∩ R).filter fun u => Smallest G R u v σ) ≤
      #((remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)).filter
        (v ∈ ·)) := by
  rcases Nat.lt_or_ge
      #((G.neighborFinset v ∩ R).filter fun u => Smallest G R u v σ) 1 with h0 | h1
  · rw [Nat.lt_one_iff.1 h0, mul_zero]
    exact Nat.zero_le _
  obtain ⟨u, hu⟩ := card_pos.1 h1
  rw [le_antisymm (card_filter_smallest_le_one G R v σ) h1, mul_one]
  rw [mem_filter, mem_inter, SimpleGraph.mem_neighborFinset] at hu
  have hvout := not_mem_lubyRemaining_of_smallest G hu.1.2 hu.1.1.symm hu.2
  refine card_le_card_of_injOn (fun w => s(v, w)) (fun w hw => ?_) (fun w _ w' _ h => ?_)
  · rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe, SimpleGraph.mem_neighborFinset] at hw
    rw [coe_filter]
    refine ⟨mem_sdiff.2 ⟨mem_filter.2 ⟨SimpleGraph.mem_edgeFinset.2 hw.1, fun x hx => ?_⟩,
      fun h => hvout ((mem_filter.1 h).2 v (Sym2.mem_mk_left v w))⟩, Sym2.mem_mk_left v w⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    exacts [hv, hw.2]
  · exact Sym2.congr_right.1 h

/- Each removed edge has at most two endpoints among the remaining vertices. -/
private theorem sum_card_filter_mem_le (R : Finset (Fin n)) (D : Finset (Sym2 (Fin n))) :
    ∑ v ∈ R, #(D.filter (v ∈ ·)) ≤ 2 * #D := by
  simp only [card_filter]
  rw [sum_comm, card_eq_sum_ones, mul_sum, mul_one]
  refine sum_le_sum fun e _ => ?_
  rw [← card_filter]
  induction e using Sym2.ind with
  | _ a b =>
    refine (card_le_card (t := {a, b}) fun x hx => ?_).trans card_le_two
    rcases Sym2.mem_iff.1 (mem_filter.1 hx).2 with rfl | rfl <;> simp

/- Luby's counting argument for one round: `n!` times the number of remaining edges is at most
twice the total number of removed edges over all permutations. -/
private theorem factorial_mul_card_le (R : Finset (Fin n)) :
    n ! * #(remainingEdges G R) ≤ 2 * ∑ σ : Equiv.Perm (Fin n),
      #(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) := by
  set d : Fin n → ℕ := fun v => #(G.neighborFinset v ∩ R) with hd
  -- the counting form, summed over the permutations
  have hcount : ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R,
      d v * #(univ.filter (Smallest G R u v)) ≤ 2 * ∑ σ : Equiv.Perm (Fin n),
        #(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) := by
    have h1 : ∀ σ : Equiv.Perm (Fin n), ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R,
        d v * (if Smallest G R u v σ then 1 else 0) ≤ 2 *
          #(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) := by
      intro σ
      refine le_trans ?_ (sum_card_filter_mem_le R _)
      refine sum_le_sum fun v hv => ?_
      rw [← mul_sum, sum_boole, Nat.cast_id]
      exact card_mul_filter_smallest_le G R hv σ
    calc ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R, d v * #(univ.filter (Smallest G R u v))
        = ∑ σ : Equiv.Perm (Fin n), ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R,
            d v * (if Smallest G R u v σ then 1 else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun v _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun u _ => ?_
          rw [← mul_sum, sum_boole, Nat.cast_id]
      _ ≤ ∑ σ : Equiv.Perm (Fin n), 2 *
            #(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) :=
          sum_le_sum fun σ _ => h1 σ
      _ = _ := (mul_sum _ _ _).symm
  -- the symmetrization: `∑_{(u, v)} d(v) / (d(u) + d(v)) = |E|` over ordered remaining edges
  set f : Fin n → Fin n → ℝ := fun u v => (d v : ℝ) / (d u + d v) with hf
  have hpos : ∀ v ∈ R, ∀ u ∈ R, G.Adj v u → (0 : ℝ) < d u + d v := by
    intro v hv u hu hvu
    have : 0 < d v := card_pos.2 ⟨u, mem_inter.2 ⟨(G.mem_neighborFinset v u).2 hvu, hu⟩⟩
    positivity
  have hsym : ∑ v ∈ R, ∑ u ∈ R, (if G.Adj v u then f u v else 0) =
      ∑ v ∈ R, ∑ u ∈ R, (if G.Adj v u then f v u else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun v _ => sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj v u
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right fun h' => h h'.symm, ite_eq_right h]
  have htwo : 2 * ∑ v ∈ R, ∑ u ∈ R, (if G.Adj v u then f u v else 0) =
      2 * (#(remainingEdges G R) : ℝ) := by
    rw [two_mul]
    nth_rewrite 2 [hsym]
    rw [← sum_add_distrib]
    have : ∀ v ∈ R, ∑ u ∈ R, (if G.Adj v u then f u v else 0) +
        ∑ u ∈ R, (if G.Adj v u then f v u else 0) = (d v : ℝ) := by
      intro v hv
      rw [← sum_add_distrib]
      have : ∀ u ∈ R, ((if G.Adj v u then f u v else 0) + if G.Adj v u then f v u else 0) =
          if G.Adj v u then (1 : ℝ) else 0 := by
        intro u hu
        split_ifs with hvu
        · have h1 := hpos v hv u hu hvu
          have h2 : (d v : ℝ) + d u ≠ 0 := by linarith
          rw [hf]
          simp only
          rw [div_add_div _ _ h1.ne' h2, div_eq_one_iff_eq (mul_ne_zero h1.ne' h2)]
          ring
        · simp
      rw [sum_congr rfl this, sum_boole]
      simp only [hd, neighborFinset_inter_eq_filter]
    rw [sum_congr rfl this]
    have := sum_card_neighbor_inter G R
    exact_mod_cast this
  have hF : ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R, f u v = (#(remainingEdges G R) : ℝ) := by
    have h := htwo
    simp only [← sum_filter, ← neighborFinset_inter_eq_filter] at h
    linarith
  -- comparing term by term with the key estimate
  have hterm : ∀ v ∈ R, ∀ u ∈ G.neighborFinset v ∩ R,
      (n ! : ℝ) * f u v ≤ d v * #(univ.filter (Smallest G R u v)) := by
    intro v hv u hu
    rw [mem_inter, SimpleGraph.mem_neighborFinset] at hu
    have hp := hpos v hv u hu.2 hu.1
    have hk : (n ! : ℝ) ≤ #(univ.filter (Smallest G R u v)) * (d u + d v) := by
      exact_mod_cast card_smallest_mul_ge G hu.2 hu.1.symm
    rw [hf]
    simp only
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) (d v)]
  have hreal : (n ! : ℝ) * #(remainingEdges G R) ≤ 2 * ∑ σ : Equiv.Perm (Fin n),
      (#(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) : ℝ) := by
    rw [← hF, mul_sum]
    calc ∑ v ∈ R, (n ! : ℝ) * ∑ u ∈ G.neighborFinset v ∩ R, f u v
        = ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R, (n ! : ℝ) * f u v :=
          sum_congr rfl fun v _ => mul_sum _ _ _
      _ ≤ ∑ v ∈ R, ∑ u ∈ G.neighborFinset v ∩ R,
            ((d v * #(univ.filter (Smallest G R u v)) : ℕ) : ℝ) := by
          refine sum_le_sum fun v hv => sum_le_sum fun u hu => ?_
          push_cast
          exact hterm v hv u hu
      _ ≤ _ := by exact_mod_cast hcount
  exact_mod_cast hreal

/- The counting form of the halving of the remaining edges in one round. -/
private theorem two_mul_sum_card_remainingEdges_le (R : Finset (Fin n)) :
    2 * ∑ σ : Equiv.Perm (Fin n), #(remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) ≤
      n ! * #(remainingEdges G R) := by
  have h1 := factorial_mul_card_le G R
  have h2 : ∑ σ : Equiv.Perm (Fin n),
      (#(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) +
        #(remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R))) =
      n ! * #(remainingEdges G R) := by
    rw [sum_congr rfl fun σ _ => card_sdiff_add_card_eq_card
      (remainingEdges_mono G (lubyRemaining_subset G _ R)), sum_const, card_univ,
      Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  rw [sum_add_distrib] at h2
  omega

private theorem uniformOn_univ_real_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] (a : α) :
    (uniformOn (Set.univ : Set α)).real {a} = (Fintype.card α : ℝ)⁻¹ := by
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_natCast, one_div]

/-- **Key estimate of Luby's analysis.** Let $G$ be a graph on $\{0, \dots, n-1\}$, let $R$ be a
set of vertices, write $N_R(w)$ for the set of neighbors of a vertex $w$ in $R$ and
$d_R(w) = |N_R(w)|$, and let $uv$ be an edge of $G$ with $u \in R$. For a uniformly random
permutation $\sigma$ of the vertices, the probability that $\sigma(u) < \sigma(w)$ for every
$w \in N_R(u) \cup N_R(v)$ other than $u$, that is, that $u$ has the smallest value in
$N_R(u) \cup N_R(v)$, is at least $1/(d_R(u) + d_R(v))$.

The uniform measure on the permutations is taken for any measurable structure on them in which
singletons are measurable; it does not depend on that structure. -/
theorem inv_le_uniformOn_smallest [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] {R : Finset (Fin n)} {u v : Fin n}
    (hu : u ∈ R) (huv : G.Adj u v) :
    ((#(G.neighborFinset u ∩ R) + #(G.neighborFinset v ∩ R) : ℕ) : ℝ≥0∞)⁻¹ ≤
      uniformOn Set.univ {σ : Equiv.Perm (Fin n) |
        ∀ w ∈ G.neighborFinset u ∩ R ∪ G.neighborFinset v ∩ R, w ≠ u → σ u < σ w} := by
  have hmem : u ∈ G.neighborFinset u ∩ R ∪ G.neighborFinset v ∩ R :=
    mem_union_right _ (mem_inter.2 ⟨(G.mem_neighborFinset v u).2 huv.symm, hu⟩)
  set S := G.neighborFinset u ∩ R ∪ G.neighborFinset v ∩ R with hS
  set A := univ.filter fun σ : Equiv.Perm (Fin n) => ∀ w ∈ S, w ≠ u → σ u < σ w with hA
  have hset : {σ : Equiv.Perm (Fin n) | ∀ w ∈ S, w ≠ u → σ u < σ w} = (A : Set _) := by
    ext σ
    simp [hA]
  have hmul := card_smallest_mul S hmem
  rw [← hA] at hmul
  have hA0 : (#A : ℝ≥0∞) ≠ 0 := by
    have : #A ≠ 0 := fun h => by rw [h, zero_mul] at hmul; exact Nat.factorial_ne_zero n hmul.symm
    exact_mod_cast this
  have hdiv : (#A : ℝ≥0∞) / (#A * #S) = (#S : ℝ≥0∞)⁻¹ := by
    calc (#A : ℝ≥0∞) / (#A * #S) = (#A * 1) / (#A * #S) := by rw [mul_one]
      _ = 1 / #S := ENNReal.mul_div_mul_left _ _ hA0 (ENNReal.natCast_ne_top _)
      _ = (#S : ℝ≥0∞)⁻¹ := one_div _
  rw [hset, uniformOn_univ, Measure.count_apply_finset, Fintype.card_perm, Fintype.card_fin,
    ← hmul, Nat.cast_mul, hdiv]
  exact ENNReal.inv_le_inv.2 (by exact_mod_cast card_union_le _ _)

/- **Luby's algorithm removes half the edges in expectation.** Let $G$ be a graph on
$\{0, \dots, n-1\}$ and let $R$ be the set of remaining vertices. Run one round of Luby's
algorithm on $R$ with the values of a uniformly random permutation $\sigma$ of the vertices, the
vertex $v$ getting the value $\sigma(v)$. The expected number of removed edges, the edges of $G$
with both endpoints in $R$ and at least one endpoint removed, is at least half the number of
edges of $G$ with both endpoints in $R$.

The uniform measure on the permutations is taken for any measurable structure on them in which
singletons are measurable; it does not depend on that structure. -/
theorem expected_removed_edges_ge [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (R : Finset (Fin n)) :
    (#(remainingEdges G R) : ℝ) / 2 ≤
      ∫ σ : Equiv.Perm (Fin n), (#(remainingEdges G R \
        remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) : ℝ) ∂uniformOn Set.univ := by
  rw [integral_fintype Integrable.of_finite]
  simp only [uniformOn_univ_real_singleton, smul_eq_mul, ← mul_sum, Fintype.card_perm,
    Fintype.card_fin]
  have h := factorial_mul_card_le G R
  have hpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ two_pos, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
  have : (n ! : ℝ) * #(remainingEdges G R) ≤ 2 * ∑ σ : Equiv.Perm (Fin n),
      (#(remainingEdges G R \ remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) : ℝ) := by
    exact_mod_cast h
  linarith

/-! ### The number of rounds -/

/- The algorithm run from the state `s` with the permutations `ω` as priorities. -/
private def runFrom (s : Finset (Fin n) × Finset (Fin n)) {k : ℕ}
    (ω : Fin k → Equiv.Perm (Fin n)) : Finset (Fin n) × Finset (Fin n) :=
  (List.ofFn fun t w => (ω t w : ℕ)).foldl (lubyRound G) s

private theorem runFrom_cons (s : Finset (Fin n) × Finset (Fin n)) {k : ℕ}
    (σ : Equiv.Perm (Fin n)) (ω : Fin k → Equiv.Perm (Fin n)) :
    runFrom G s (Fin.cons σ ω : Fin (k + 1) → Equiv.Perm (Fin n)) =
      runFrom G (lubyRound G s fun w => (σ w : ℕ)) ω := by
  simp [runFrom, List.ofFn_succ]

/- A round that starts with no remaining edge removes every remaining vertex. -/
private theorem lubyRemaining_eq_empty_of_remainingEdges (prio : Fin n → ℕ)
    {R : Finset (Fin n)} (h : remainingEdges G R = ∅) : lubyRemaining G prio R = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => ?_
  rw [lubyRemaining, mem_filter] at hv
  refine hv.2.1 (mem_filter.2 ⟨hv.1, fun u hu => ?_⟩)
  rw [mem_inter, SimpleGraph.mem_neighborFinset] at hu
  have : s(v, u) ∈ remainingEdges G R := by
    refine mem_filter.2 ⟨SimpleGraph.mem_edgeFinset.2 hu.1, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    exacts [hv.1, hu.2]
  simp [h] at this

/- The counting form of the bound on the rounds. -/
private theorem card_nonempty_mul_le (T : ℕ) (s : Finset (Fin n) × Finset (Fin n)) :
    (∑ ω : Fin (T + 1) → Equiv.Perm (Fin n), if (runFrom G s ω).2.Nonempty then 1 else 0) *
      2 ^ T ≤ n ! ^ (T + 1) * #(remainingEdges G s.2) := by
  induction T generalizing s with
  | zero =>
    rw [pow_zero, mul_one]
    rcases Nat.eq_zero_or_pos #(remainingEdges G s.2) with h | h
    · rw [h, mul_zero]
      refine (sum_eq_zero fun ω _ => ?_).le
      have : (runFrom G s ω).2 = ∅ := by
        rw [← Fin.cons_self_tail ω, runFrom_cons]
        simp only [runFrom, List.ofFn_zero, List.foldl_nil, lubyRound]
        exact lubyRemaining_eq_empty_of_remainingEdges G _ (card_eq_zero.1 h)
      simp [this]
    · calc (∑ ω : Fin (0 + 1) → Equiv.Perm (Fin n),
            if (runFrom G s ω).2.Nonempty then 1 else 0)
          ≤ ∑ _ω : Fin (0 + 1) → Equiv.Perm (Fin n), 1 :=
            sum_le_sum fun ω _ => by split_ifs <;> simp
        _ = n ! ^ (0 + 1) := by
            simp [Fintype.card_pi, Fintype.card_perm]
        _ ≤ n ! ^ (0 + 1) * #(remainingEdges G s.2) := Nat.le_mul_of_pos_right _ h
  | succ T ih =>
    have hsplit : (∑ ω : Fin (T + 1 + 1) → Equiv.Perm (Fin n),
        if (runFrom G s ω).2.Nonempty then 1 else 0) =
        ∑ σ : Equiv.Perm (Fin n), ∑ ω : Fin (T + 1) → Equiv.Perm (Fin n),
          if (runFrom G (lubyRound G s fun w => (σ w : ℕ)) ω).2.Nonempty then 1 else 0 := by
      rw [← Fintype.sum_prod_type']
      refine (Fintype.sum_equiv (Fin.consEquiv fun _ => Equiv.Perm (Fin n)) _ _ ?_).symm
      intro p
      simp only [Fin.consEquiv_apply, runFrom_cons]
    rw [hsplit]
    calc (∑ σ : Equiv.Perm (Fin n), ∑ ω : Fin (T + 1) → Equiv.Perm (Fin n),
            if (runFrom G (lubyRound G s fun w => (σ w : ℕ)) ω).2.Nonempty then 1 else 0) *
              2 ^ (T + 1)
        = ∑ σ : Equiv.Perm (Fin n), (∑ ω : Fin (T + 1) → Equiv.Perm (Fin n),
            if (runFrom G (lubyRound G s fun w => (σ w : ℕ)) ω).2.Nonempty then 1 else 0) *
              2 ^ T * 2 := by
          rw [sum_mul]
          exact sum_congr rfl fun σ _ => by ring
      _ ≤ ∑ σ : Equiv.Perm (Fin n), n ! ^ (T + 1) *
            #(remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) s.2)) * 2 :=
          sum_le_sum fun σ _ => Nat.mul_le_mul_right 2 (ih _)
      _ = n ! ^ (T + 1) * (2 * ∑ σ : Equiv.Perm (Fin n),
            #(remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) s.2))) := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun σ _ => ?_
          ring
      _ ≤ n ! ^ (T + 1) * (n ! * #(remainingEdges G s.2)) :=
          Nat.mul_le_mul_left _ (two_mul_sum_card_remainingEdges_le G s.2)
      _ = n ! ^ (T + 1 + 1) * #(remainingEdges G s.2) := by ring

private theorem remainingEdges_univ : remainingEdges G univ = G.edgeFinset := by
  simp [remainingEdges]

/- **Luby's algorithm terminates quickly with high probability.** Let $G$ be a graph on
$\{0, \dots, n-1\}$ with edge set $E$, and run Luby's algorithm for $T + 1$ rounds, the values
of round $t$ being those of a permutation $\sigma_t$ of the vertices, the vertex $v$ getting the
value $\sigma_t(v)$, where $\sigma_0, \dots, \sigma_T$ are independent and uniformly random.
The probability that some vertex still remains is at most $|E| / 2^T$.

The uniform measure on the permutations is taken for any measurable structure on them in which
singletons are measurable; it does not depend on that structure. -/
theorem prob_lubyRun_nonempty_le [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (T : ℕ) :
    Measure.pi (fun _ : Fin (T + 1) => uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
        {ω | (lubyRun G (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} ≤
      #G.edgeFinset / 2 ^ T := by
  rw [← uniformOn_pi, Set.pi_univ, uniformOn_univ]
  have hset : {ω : Fin (T + 1) → Equiv.Perm (Fin n) |
      (lubyRun G (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} =
      ((univ.filter fun ω : Fin (T + 1) → Equiv.Perm (Fin n) =>
        (runFrom G (∅, univ) ω).2.Nonempty : Finset _) : Set _) := by
    ext ω
    simp [runFrom, lubyRun]
  have h := card_nonempty_mul_le G T (∅, univ)
  rw [← card_filter, remainingEdges_univ] at h
  rw [hset, Measure.count_apply_finset, Fintype.card_pi, prod_const, card_univ,
    Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
  have hT : (2 : ℝ≥0∞) ^ T ≠ 0 := pow_ne_zero _ two_ne_zero
  have hT' : (2 : ℝ≥0∞) ^ T ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm, ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hT) (Or.inl hT')]
  exact_mod_cast h

/- **Luby's algorithm terminates in $O(\log n)$ rounds with high probability.** Let $G$ be a
graph on $\{0, \dots, n-1\}$, let $c$ be a natural number, and run Luby's algorithm for
$(c + 2) \lceil \log_2 n \rceil + 1$ rounds, the values of round $t$ being those of a permutation
$\sigma_t$ of the vertices, the vertex $v$ getting the value $\sigma_t(v)$, where the $\sigma_t$
are independent and uniformly random. The probability that some vertex still remains is at most
$1/n^c$.

Here $\lceil \log_2 n \rceil$ is the least $k$ with $n \le 2^k$, and $1/0^c = \infty$ for
$c \ge 1$. The uniform measure on the permutations is taken for any measurable structure on them
in which singletons are measurable; it does not depend on that structure. -/
theorem prob_lubyRun_nonempty_le_inv_pow [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (c : ℕ) :
    Measure.pi (fun _ : Fin ((c + 2) * Nat.clog 2 n + 1) =>
        uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
        {ω | (lubyRun G (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} ≤
      ((n : ℝ≥0∞) ^ c)⁻¹ := by
  refine (prob_lubyRun_nonempty_le G _).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : #G.edgeFinset = 0 := by
      refine card_eq_zero.2 (eq_empty_of_forall_notMem fun e he => ?_)
      induction e using Sym2.ind with
      | _ a b => exact a.elim0
    simp [this]
  have hE : #G.edgeFinset * n ^ c ≤ 2 ^ ((c + 2) * Nat.clog 2 n) := by
    calc #G.edgeFinset * n ^ c ≤ n ^ 2 * n ^ c := by
          refine Nat.mul_le_mul_right _ ?_
          refine (SimpleGraph.card_edgeFinset_le_card_choose_two).trans ?_
          rw [Fintype.card_fin]
          exact Nat.choose_le_pow n 2
      _ = n ^ (c + 2) := by ring
      _ ≤ (2 ^ Nat.clog 2 n) ^ (c + 2) := Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two n) _
      _ = 2 ^ ((c + 2) * Nat.clog 2 n) := by ring
  have hT : (2 : ℝ≥0∞) ^ ((c + 2) * Nat.clog 2 n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hT' : (2 : ℝ≥0∞) ^ ((c + 2) * Nat.clog 2 n) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hn0 : ((n : ℝ≥0∞) ^ c) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  have hnt : ((n : ℝ≥0∞) ^ c) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
  rw [ENNReal.div_le_iff hT hT', ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl hnt)]
  exact_mod_cast hE

/-- **Luby's maximal independent set algorithm.** Let $G$ be a graph on $\{0, \dots, n-1\}$ with
edge set $E$. In each round of Luby's algorithm, every remaining vertex $v$ gets a value
$\pi(v)$; the remaining vertices whose value is smaller than that of every remaining neighbor
join the independent set $I$ (in particular every remaining vertex with no remaining neighbor
does), and they and their neighbors are removed, together with their incident edges.

1. For any values $\pi_t(v) \in \mathbb{N}$, ties broken by vertex index: once no vertex remains,
   $I$ is a maximal independent set of $G$ and further rounds change nothing; and no vertex
   remains after $n$ rounds.
2. Let the values of a round be those of a uniformly random permutation $\sigma$ of the vertices,
   the vertex $v$ getting the value $\sigma(v)$. For every set $R$ of remaining vertices, the
   expected number of edges removed by the round (edges of $G$ with both endpoints in $R$ and at
   least one endpoint removed) is at least half the number of edges of $G$ with both endpoints in
   $R$.
3. Let the values of the rounds be those of independent uniformly random permutations
   $\sigma_0, \sigma_1, \dots$ of the vertices. For every $T \in \mathbb{N}$, some vertex remains
   after $T + 1$ rounds with probability at most $|E| / 2^T$. In particular, for every
   $c \in \mathbb{N}$, some vertex remains after $(c + 2) \lceil \log_2 n \rceil + 1$ rounds with
   probability at most $1/n^c$, where $\lceil \log_2 n \rceil$ is the least $k$ with $n \le 2^k$
   and $1/0^c = \infty$ for $c \ge 1$.

The uniform measure on the permutations is taken for any measurable structure on them in which
singletons are measurable; it does not depend on that structure. -/
theorem luby_mis [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] :
    (∀ prios : List (Fin n → ℕ),
      ((lubyRun G prios).2 = ∅ →
          Maximal G.IsIndepSet ((lubyRun G prios).1 : Set (Fin n)) ∧
            ∀ prios' : List (Fin n → ℕ), lubyRun G (prios ++ prios') = lubyRun G prios) ∧
        (n ≤ prios.length → (lubyRun G prios).2 = ∅)) ∧
    (∀ R : Finset (Fin n), (#(remainingEdges G R) : ℝ) / 2 ≤
      ∫ σ : Equiv.Perm (Fin n), (#(remainingEdges G R \
        remainingEdges G (lubyRemaining G (fun w => (σ w : ℕ)) R)) : ℝ) ∂uniformOn Set.univ) ∧
    (∀ T : ℕ,
      Measure.pi (fun _ : Fin (T + 1) => uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
          {ω | (lubyRun G (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} ≤
        #G.edgeFinset / 2 ^ T) ∧
    (∀ c : ℕ,
      Measure.pi (fun _ : Fin ((c + 2) * Nat.clog 2 n + 1) =>
          uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
          {ω | (lubyRun G (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} ≤
        ((n : ℝ≥0∞) ^ c)⁻¹) :=
  ⟨lubyRun_maximal G, expected_removed_edges_ge G, prob_lubyRun_nonempty_le G,
    prob_lubyRun_nonempty_le_inv_pow G⟩

end Cslib.Distributed.LubyMIS
