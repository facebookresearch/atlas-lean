/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.FinRange
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Maximum bipartite matching by augmenting paths

The augmenting-path method for maximum matching in a bipartite graph (CLRS, third edition,
Section 26.3; the phase structure of Hopcroft and Karp is built on the same paths): starting from
the empty matching, repeatedly find an augmenting path (an alternating path between an unmatched
left vertex and an unmatched right vertex) and flip it, which grows the matching by one edge; stop
when there is none.

The graph has left vertices `Fin a`, right vertices `Fin b` and adjacency lists
`adj : Fin a → List (Fin b)`. The matching is kept as `mate : Fin b → Option (Fin a)`, the partner
of each right vertex.

* Search (`layers`): the alternating breadth-first layers from the unmatched left vertices: a
  right vertex is reached through a non-matching edge from a reached left vertex, and a left vertex
  through its matching edge from a reached right vertex.
* Augmentation (`augment`): if an unmatched right vertex is reached, walk the layers back to an
  unmatched left vertex (`pathTo`) and flip the path (`flip`).
* `maxMatching adj`: augment until no unmatched right vertex is reached.

Main results: `isMatching_maxMatching` (the result is a matching) and `card_le_maxMatching`
(no matching is larger). Along the way: `pathTo_spec` (the walk back is an alternating path to an
unmatched left vertex, `AltPath`), `pathTo_isAugmentingPath` (an augmenting path when the right
vertex it starts from is unmatched), `valid_flip` and `card_matched_flip` (flipping it gives a
matching with one more edge), and `card_le_of_no_free`, the optimality certificate: when the
search reaches no unmatched right vertex, the unreached left vertices together with the reached
right vertices cover every edge (Kőnig's vertex cover), and each of them is matched to a distinct
matching edge.

## Hopcroft–Karp phases

`hopcroftKarp adj` runs phases (Hopcroft and Karp, *An n^{5/2} algorithm for maximum matchings in
bipartite graphs*, SIAM J. Comput. 1973): one search computes the layers, and `phase` collects
vertex-disjoint augmenting paths from the unmatched right vertices reached in the earliest round
that reaches any (`firstFreeRound`), trying each candidate once with a depth-first search over the
layers through the vertices not yet used (`searchPath`, `tryPreds`, `phaseAux`), where a right
vertex from which a search fails is marked dead and not searched again in that phase (Hopcroft and
Karp's pruning); `hkStep` flips the paths all at once. `isMatching_hopcroftKarp` and
`card_le_hopcroftKarp` are its correctness. Along the way: `searchPath_spec` (a found path is
alternating and avoids the used and dead vertices), `searchPath_mono` (the dead set only grows),
`searchPath_isSome` (with nothing used or dead, every reached right vertex yields a path),
`phaseAux_spec` (the paths are augmenting and pairwise vertex-disjoint), `valid_flip_flatten` and
`card_matched_flip_flatten` (flipping them gives a matching with at least one more edge), and
`phase_ne_nil` (a phase finds a path whenever the search reaches an unmatched right vertex).
Phases use shortest augmenting paths, as Hopcroft and Karp require: every augmenting path has at
least `d + 1` pairs, where `d` is `firstFreeRound` (`le_length_of_isAugmentingPath`, via
`mem_layers_length`), and every path of a phase has exactly `d + 1` (`length_of_mem_phase`). The
paths of a phase form a maximal set of vertex-disjoint shortest augmenting paths: every shortest
augmenting path shares a vertex with one of them (`phase_maximal`). The key step is
`searchPath_dead`: a right vertex that a search marks dead has no shortest escape avoiding the used
and dead vertices (`NoEscape`), so the pruning loses no path. Distances do not decrease across a
phase: every vertex reached by round `k` after the flip was reached by round `k` before
(`layers_flip_phase_subset`), and the next phase's paths are strictly longer
(`lt_firstFreeRound_flip_phase`): a shortest augmenting path of the same length after the phase
would be a shortest augmenting chain before it that avoids the phase's paths
(`chain_of_chain_flip_phase`), against maximality. Hence `O(√V)` phases: from the empty matching,
`2 ⌊√b⌋ + 2` phases reach a maximum matching (`card_le_hopcroftKarpAux_sqrt`). After `t` phases
every augmenting path has more than `t` pairs (`firstFreeRound_hopcroftKarpAux`), and then the
deficit against any matching is at most `b / t` (`mul_card_sub_le`: per round of the search, the
unreached left vertices and the reached right vertices cover every edge, in place of Hopcroft and
Karp's symmetric-difference count); each further phase adds an edge.

## Cost model

None is claimed beyond the number of phases (`card_le_hopcroftKarpAux_sqrt`). This module proves
correctness; the layers are recomputed with `Finset` filters over all vertices, so the programs
are polynomial, not the `O(V E)` of the textbook method or the `O(√V E)` of Hopcroft and Karp.
Within a phase, `searchPath` explores each right vertex at most once: a failed search marks it
dead, and a successful one ends the search and marks its path used.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BipartiteMatching

variable {a b : ℕ} (adj : Fin a → List (Fin b))

/-- A matching: a set of edges `(i, j)` (with `j ∈ adj i`) in which no left and no right vertex
occurs twice. -/
structure IsMatching (M : Finset (Fin a × Fin b)) : Prop where
  /-- Every pair is an edge. -/
  edge : ∀ p ∈ M, p.2 ∈ adj p.1
  /-- No left vertex is matched twice. -/
  left : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q
  /-- No right vertex is matched twice. -/
  right : ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q

/-- The matched pairs of a partner array. -/
def pairs (mate : Fin b → Option (Fin a)) : Finset (Fin a × Fin b) :=
  Finset.univ.filter fun p => mate p.2 = some p.1

/-- A partner array describes a matching: partners are neighbours, and no left vertex is the
partner of two right vertices. -/
structure Valid (mate : Fin b → Option (Fin a)) : Prop where
  /-- Partners are neighbours. -/
  edge : ∀ i j, mate j = some i → j ∈ adj i
  /-- No left vertex is the partner of two right vertices. -/
  inj : ∀ i j j', mate j = some i → mate j' = some i → j = j'

/-- `i` is unmatched. -/
def Free (mate : Fin b → Option (Fin a)) (i : Fin a) : Prop := ∀ j, mate j ≠ some i

instance (mate : Fin b → Option (Fin a)) (i : Fin a) : Decidable (Free mate i) := by
  unfold Free; infer_instance

/-- The alternating breadth-first layers, cumulative on both sides: `(layers adj mate k).1` are the
left vertices reached within `k` rounds (initially the unmatched ones), and `(layers adj mate k).2`
the right vertices reached within `k` rounds (through a non-matching edge from a left vertex
reached within `k - 1` rounds). The round where a vertex is first reached is its breadth-first
level; `pathTo` descends to it. -/
def layers (mate : Fin b → Option (Fin a)) : ℕ → Finset (Fin a) × Finset (Fin b)
  | 0 => (Finset.univ.filter fun i => Free mate i, ∅)
  | k + 1 =>
      let Z := (layers mate k).1
      let R := Finset.univ.filter fun j => ∃ i ∈ Z, j ∈ adj i ∧ mate j ≠ some i
      (Z ∪ Finset.univ.filter (fun i => ∃ j ∈ R, mate j = some i), R)

section Layers

variable {adj} {mate : Fin b → Option (Fin a)}

theorem mem_layers_zero_fst {i : Fin a} : i ∈ (layers adj mate 0).1 ↔ Free mate i := by
  simp [layers]

theorem layers_zero_snd : (layers adj mate 0).2 = ∅ := rfl

theorem mem_layers_succ_snd {k : ℕ} {j : Fin b} : j ∈ (layers adj mate (k + 1)).2 ↔
    ∃ i ∈ (layers adj mate k).1, j ∈ adj i ∧ mate j ≠ some i := by
  simp [layers]

theorem mem_layers_succ_fst {k : ℕ} {i : Fin a} : i ∈ (layers adj mate (k + 1)).1 ↔
    i ∈ (layers adj mate k).1 ∨ ∃ j ∈ (layers adj mate (k + 1)).2, mate j = some i := by
  simp only [layers, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

theorem layers_fst_mono {k m : ℕ} (h : k ≤ m) : (layers adj mate k).1 ⊆ (layers adj mate m).1 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans fun i hi => mem_layers_succ_fst.2 (Or.inl hi)

theorem layers_snd_mono {k m : ℕ} (h : k ≤ m) : (layers adj mate k).2 ⊆ (layers adj mate m).2 := by
  cases k with
  | zero => simp [layers_zero_snd]
  | succ k =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      intro j hj
      obtain ⟨i, hi, h1, h2⟩ := mem_layers_succ_snd.1 hj
      exact mem_layers_succ_snd.2 ⟨i, layers_fst_mono (by omega) hi, h1, h2⟩

/-- A reached left vertex that is matched was reached through its partner. -/
theorem exists_mate_of_mem_layers {k : ℕ} {i : Fin a} (hi : i ∈ (layers adj mate k).1)
    (hfree : ¬ Free mate i) : ∃ j ∈ (layers adj mate k).2, mate j = some i := by
  induction k with
  | zero => exact absurd (mem_layers_zero_fst.1 hi) hfree
  | succ k ih =>
      rcases mem_layers_succ_fst.1 hi with hi | h
      · obtain ⟨j, hj, hm⟩ := ih hi
        exact ⟨j, layers_snd_mono (Nat.le_succ k) hj, hm⟩
      · exact h

/-- Once two consecutive left layers agree, the layers stop growing. -/
theorem layers_fst_eq_of_eq {k : ℕ} (h : (layers adj mate k).1 = (layers adj mate (k + 1)).1) :
    ∀ m, k ≤ m → (layers adj mate m).1 = (layers adj mate k).1 := by
  intro m hm
  induction hm with
  | refl => rfl
  | @step m hkm ih =>
      -- the right layer after `m` equals the one after `m - 1`
      have hR : (layers adj mate (m + 1)).2 ⊆ (layers adj mate (k + 1)).2 := by
        intro j hj
        obtain ⟨i, hi, h1, h2⟩ := mem_layers_succ_snd.1 hj
        exact mem_layers_succ_snd.2 ⟨i, by rw [ih] at hi; exact hi, h1, h2⟩
      refine le_antisymm (fun i hi => ?_) (ih ▸ layers_fst_mono (Nat.le_succ m))
      rcases mem_layers_succ_fst.1 hi with hi | ⟨j, hj, hm⟩
      · rwa [ih] at hi
      · rw [h]; exact mem_layers_succ_fst.2 (Or.inr ⟨j, hR hj, hm⟩)

/-- The left layers are stable after `a` rounds. -/
theorem layers_fst_stable : (layers adj mate (a + 1)).1 = (layers adj mate a).1 := by
  by_cases h : ∃ k ≤ a, (layers adj mate k).1 = (layers adj mate (k + 1)).1
  · obtain ⟨k, hk, hkk⟩ := h
    rw [layers_fst_eq_of_eq hkk (a + 1) (by omega), layers_fst_eq_of_eq hkk a hk]
  · push Not at h
    have hgrow : ∀ k ≤ a + 1, k ≤ (layers adj mate k).1.card := by
      intro k hk
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
          have hlt : (layers adj mate k).1.card < (layers adj mate (k + 1)).1.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
              ⟨layers_fst_mono (Nat.le_succ k), h k (by omega)⟩)
          have := ih (by omega)
          omega
    have h1 := hgrow (a + 1) le_rfl
    have h2 : (layers adj mate (a + 1)).1.card ≤ a := by
      simpa using Finset.card_le_univ (layers adj mate (a + 1)).1
    omega

end Layers

/-! ## Augmenting paths -/

/-- Walk the layers back from a reached right vertex `j` (reached by round `k + 1`): go down to
the round where `j` is first reached, take a predecessor `i` of the round before, and, unless `i`
is unmatched, continue from the partner of `i`. The result lists the pairs to match, `j` first. -/
def pathTo (mate : Fin b → Option (Fin a)) : ℕ → Fin b → List (Fin a × Fin b)
  | 0, j =>
      let Z := (layers adj mate 0).1
      match (List.finRange a).find? (fun i => decide (i ∈ Z ∧ j ∈ adj i ∧ mate j ≠ some i)) with
      | none => []
      | some i => [(i, j)]
  | k + 1, j =>
      let L := layers adj mate (k + 1)
      if j ∈ L.2 then pathTo mate k j
      else
        match (List.finRange a).find? (fun i =>
          decide (i ∈ L.1 ∧ j ∈ adj i ∧ mate j ≠ some i)) with
        | none => []
        | some i =>
            match (List.finRange b).find? (fun j' => decide (mate j' = some i)) with
            | none => [(i, j)]
            | some j' => (i, j) :: pathTo mate k j'

/-- Match each listed pair, keeping the other partners. -/
def flip (mate : Fin b → Option (Fin a)) (P : List (Fin a × Fin b)) : Fin b → Option (Fin a) :=
  fun j => match P.find? (fun p => decide (p.2 = j)) with
    | some p => some p.1
    | none => mate j

/-- An alternating path as listed by `pathTo`: it starts at the right vertex `j`, alternates
non-matching edges (the listed pairs) with matching edges (each listed right vertex after the
first is the partner of the previous listed left vertex), and ends at an unmatched left vertex.
It is an augmenting path when `j` is unmatched too (`IsAugmentingPath`). -/
structure AltPath (mate : Fin b → Option (Fin a)) (k : ℕ) (j : Fin b)
    (P : List (Fin a × Fin b)) : Prop where
  /-- It starts at `j`. -/
  head : P.head?.map Prod.snd = some j
  /-- Its pairs are non-matching edges. -/
  edge : ∀ p ∈ P, p.2 ∈ adj p.1 ∧ mate p.2 ≠ some p.1
  /-- Its vertices are reached. -/
  layer : ∀ p ∈ P, p.1 ∈ (layers adj mate k).1 ∧ p.2 ∈ (layers adj mate (k + 1)).2
  /-- No left vertex twice. -/
  nodup_fst : (P.map Prod.fst).Nodup
  /-- No right vertex twice. -/
  nodup_snd : (P.map Prod.snd).Nodup
  /-- Each right vertex after the first is matched to the previous left vertex. -/
  chain : List.IsChain (fun p q => mate q.2 = some p.1) P
  /-- The last left vertex is unmatched. -/
  last : ∀ p ∈ P.getLast?, Free mate p.1

/-- An augmenting path: an alternating path (`AltPath`) whose starting right vertex is unmatched,
so that both endpoints are unmatched. -/
structure IsAugmentingPath (mate : Fin b → Option (Fin a)) (k : ℕ) (j : Fin b)
    (P : List (Fin a × Fin b)) : Prop extends AltPath adj mate k j P where
  /-- The starting right vertex is unmatched. -/
  start_free : mate j = none

section Paths

variable {adj} {mate : Fin b → Option (Fin a)}

private theorem AltPath.mono {k : ℕ} {j : Fin b} {P : List (Fin a × Fin b)}
    (h : AltPath adj mate k j P) : AltPath adj mate (k + 1) j P :=
  ⟨h.head, h.edge, fun p hp => ⟨layers_fst_mono (Nat.le_succ k) (h.layer p hp).1,
    layers_snd_mono (Nat.le_succ _) (h.layer p hp).2⟩, h.nodup_fst, h.nodup_snd, h.chain, h.last⟩

private theorem mem_layers_fst_of_mate {k : ℕ} {i : Fin a} {j : Fin b}
    (hj : j ∈ (layers adj mate k).2) (hm : mate j = some i) : i ∈ (layers adj mate k).1 := by
  cases k with
  | zero => simp [layers_zero_snd] at hj
  | succ k => exact mem_layers_succ_fst.2 (Or.inr ⟨j, hj, hm⟩)

private theorem find?_some_of_exists {α : Type*} {l : List α} {q : α → Bool}
    (h : ∃ x ∈ l, q x = true) : ∃ x, l.find? q = some x := by
  cases hf : l.find? q with
  | none =>
      obtain ⟨x, hx, hq⟩ := h
      exact absurd hq (by simpa using List.find?_eq_none.1 hf x hx)
  | some x => exact ⟨x, rfl⟩

/-- `pathTo` lists an alternating path from a reached right vertex to an unmatched left
vertex. -/
theorem pathTo_spec (hv : Valid adj mate) : ∀ (k : ℕ) (j : Fin b),
    j ∈ (layers adj mate (k + 1)).2 → AltPath adj mate k j (pathTo adj mate k j)
  | 0, j, hj => by
      obtain ⟨i, hi, h1, h2⟩ := mem_layers_succ_snd.1 hj
      obtain ⟨i', hf⟩ := find?_some_of_exists (l := List.finRange a)
        (q := fun i => decide (i ∈ (layers adj mate 0).1 ∧ j ∈ adj i ∧ mate j ≠ some i))
        ⟨i, List.mem_finRange i, by simp [hi, h1, h2]⟩
      have hq := List.find?_some hf
      simp only [decide_eq_true_eq] at hq
      simp only [pathTo, hf]
      refine ⟨rfl, ?_, ?_, by simp, by simp, List.isChain_singleton _, ?_⟩
      · simp only [List.mem_singleton]; rintro p rfl; exact ⟨hq.2.1, hq.2.2⟩
      · simp only [List.mem_singleton]; rintro p rfl; exact ⟨hq.1, hj⟩
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq]
        rintro p rfl; exact mem_layers_zero_fst.1 hq.1
  | k + 1, j, hj => by
      by_cases hjk : j ∈ (layers adj mate (k + 1)).2
      · simp only [pathTo, hjk, ite_true]
        exact (pathTo_spec hv k j hjk).mono
      · obtain ⟨i, hi, h1, h2⟩ := mem_layers_succ_snd.1 hj
        obtain ⟨i', hf⟩ := find?_some_of_exists (l := List.finRange a)
          (q := fun i => decide (i ∈ (layers adj mate (k + 1)).1 ∧ j ∈ adj i ∧ mate j ≠ some i))
          ⟨i, List.mem_finRange i, by simp [hi, h1, h2]⟩
        have hq := List.find?_some hf
        simp only [decide_eq_true_eq] at hq
        obtain ⟨hi'Z, hi'adj, hi'm⟩ := hq
        -- `i'` was first reached in round `k + 1`
        have hnot : i' ∉ (layers adj mate k).1 := fun h =>
          hjk (mem_layers_succ_snd.2 ⟨i', h, hi'adj, hi'm⟩)
        have hnf : ¬ Free mate i' := fun h =>
          hnot (layers_fst_mono (Nat.zero_le k) (mem_layers_zero_fst.2 h))
        obtain ⟨j'', hj''R, hj''m⟩ := exists_mate_of_mem_layers hi'Z hnf
        obtain ⟨j', hf'⟩ := find?_some_of_exists (l := List.finRange b)
          (q := fun j' => decide (mate j' = some i')) ⟨j'', List.mem_finRange _, by simp [hj''m]⟩
        have hj'm : mate j' = some i' := by simpa using List.find?_some hf'
        have hj'eq : j' = j'' := hv.inj i' j' j'' hj'm hj''m
        subst hj'eq
        have ih := pathTo_spec hv k j' hj''R
        simp only [pathTo, hjk, ite_false, hf, hf']
        obtain ⟨hh, he, hl, hn1, hn2, hc, hlast⟩ := ih
        have hne : pathTo adj mate k j' ≠ [] := by
          intro h; rw [h] at hh; simp at hh
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨hi'adj, hi'm⟩
          · exact he p hp
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨hi'Z, hj⟩
          · exact ⟨layers_fst_mono (Nat.le_succ k) (hl p hp).1,
              layers_snd_mono (Nat.le_succ _) (hl p hp).2⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hn1⟩
          obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hmem
          have := (hl p hp).1
          rw [hpi] at this
          exact hnot this
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hn2⟩
          obtain ⟨p, hp, hpj⟩ := List.mem_map.1 hmem
          have := (hl p hp).2
          rw [hpj] at this
          exact hjk this
        · rw [List.isChain_cons]
          refine ⟨fun q hq => ?_, hc⟩
          obtain ⟨q', hq', rfl⟩ : ∃ q', (pathTo adj mate k j').head? = some q' ∧ q' = q :=
            ⟨q, hq, rfl⟩
          have : q'.2 = j' := by simpa [hq'] using hh
          simp only [this, hj'm]
        · intro p hp
          rw [List.getLast?_cons, Option.mem_def] at hp
          obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (List.getLast?_eq_none_iff.not.2 hne)
          rw [hx] at hp
          simp only [Option.getD_some, Option.some.injEq] at hp
          exact hlast p (by rw [Option.mem_def, hx, hp])

private theorem flip_eq_some {P : List (Fin a × Fin b)} (hn : (P.map Prod.snd).Nodup)
    {i : Fin a} {j : Fin b} :
    flip mate P j = some i ↔ (i, j) ∈ P ∨ ((∀ p ∈ P, p.2 ≠ j) ∧ mate j = some i) := by
  unfold flip
  cases hf : P.find? (fun p => decide (p.2 = j)) with
  | none =>
      have hall : ∀ p ∈ P, p.2 ≠ j := fun p hp h => by
        simpa [h] using List.find?_eq_none.1 hf p hp
      simp only
      constructor
      · exact fun h => Or.inr ⟨hall, h⟩
      · rintro (h | ⟨-, h⟩)
        · exact absurd rfl (hall _ h)
        · exact h
  | some p =>
      have hp := List.mem_of_find?_eq_some hf
      have hpj : p.2 = j := by simpa using List.find?_some hf
      simp only [Option.some.injEq]
      constructor
      · rintro rfl; left; rw [← hpj]; exact hp
      · rintro (h | ⟨hall, -⟩)
        · have := List.inj_on_of_nodup_map hn hp h (by simp [hpj])
          rw [this]
        · exact absurd hpj (hall p hp)

/-- In a chain, an element is the last one or has a successor. -/
private theorem last_or_succ {R : Fin a × Fin b → Fin a × Fin b → Prop} :
    ∀ {l : List (Fin a × Fin b)}, List.IsChain R l → ∀ p ∈ l,
      l.getLast? = some p ∨ ∃ q ∈ l, R p q
  | [], _, p, hp => absurd hp List.not_mem_nil
  | [x], _, p, hp => by simp only [List.mem_singleton] at hp; subst hp; simp
  | x :: y :: l, hc, p, hp => by
      rw [List.isChain_cons_cons] at hc
      rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inr ⟨y, by simp, hc.1⟩
      · rcases last_or_succ hc.2 p hp with h | ⟨q, hq, hpq⟩
        · left; rw [List.getLast?_cons_cons]; exact h
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hpq⟩

/-- In a chain, an element is the first one or has a predecessor. -/
private theorem head_or_pred {R : Fin a × Fin b → Fin a × Fin b → Prop} :
    ∀ {l : List (Fin a × Fin b)}, List.IsChain R l → ∀ q ∈ l,
      l.head? = some q ∨ ∃ p ∈ l, R p q
  | [], _, q, hq => absurd hq List.not_mem_nil
  | x :: l, hc, q, hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · simp
      · rw [List.isChain_cons] at hc
        rcases head_or_pred hc.2 q hq with h | ⟨p, hp, hpq⟩
        · exact Or.inr ⟨x, by simp, hc.1 q h⟩
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hpq⟩

/-- Flipping an alternating path from `pathTo` gives a matching. -/
theorem valid_flip (hv : Valid adj mate) {k : ℕ} {j : Fin b} {P : List (Fin a × Fin b)}
    (hP : AltPath adj mate k j P) : Valid adj (flip mate P) := by
  refine ⟨fun i j' h => ?_, fun i j₁ j₂ h₁ h₂ => ?_⟩
  · rcases (flip_eq_some hP.nodup_snd).1 h with h | ⟨-, h⟩
    · exact (hP.edge _ h).1
    · exact hv.edge i j' h
  · -- a left vertex of the path keeps exactly its new partner
    have key : ∀ j₁ j₂, (i, j₁) ∈ P → (∀ p ∈ P, p.2 ≠ j₂) → mate j₂ = some i → False := by
      intro j₁ j₂ hp hall hm
      rcases last_or_succ hP.chain _ hp with hl | ⟨q, hq, hqm⟩
      · exact hP.last _ hl j₂ hm
      · exact hall q hq (hv.inj i q.2 j₂ hqm hm)
    rcases (flip_eq_some hP.nodup_snd).1 h₁ with h₁ | ⟨hall₁, h₁⟩ <;>
      rcases (flip_eq_some hP.nodup_snd).1 h₂ with h₂ | ⟨hall₂, h₂⟩
    · have := List.inj_on_of_nodup_map hP.nodup_fst h₁ h₂ rfl
      simpa using congrArg Prod.snd this
    · exact (key _ _ h₁ hall₂ h₂).elim
    · exact (key _ _ h₂ hall₁ h₁).elim
    · exact hv.inj i j₁ j₂ h₁ h₂

/-- The matched right vertices. -/
def matched (mate : Fin b → Option (Fin a)) : Finset (Fin b) :=
  Finset.univ.filter fun j => (mate j).isSome

/-- Flipping an alternating path from `j` matches `j` in addition to the matched right vertices
(the others on the path change partners but stay matched). -/
theorem matched_flip {k : ℕ} {j : Fin b} {P : List (Fin a × Fin b)} (hP : AltPath adj mate k j P) :
    matched (flip mate P) = insert j (matched mate) := by
  ext j'
  simp only [matched, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Option.isSome_iff_exists]
  constructor
  · rintro ⟨i, h⟩
    rcases (flip_eq_some hP.nodup_snd).1 h with h | ⟨-, h⟩
    · rcases head_or_pred hP.chain _ h with hh | ⟨p, -, hpm⟩
      · left; simpa [hh] using hP.head
      · exact Or.inr ⟨_, hpm⟩
    · exact Or.inr ⟨i, h⟩
  · rintro (rfl | ⟨i, h⟩)
    · obtain ⟨p, hp⟩ : ∃ p, P.head? = some p := by
        cases hh : P.head? with
        | none => have := hP.head; rw [hh] at this; simp at this
        | some p => exact ⟨p, rfl⟩
      have hpj : p.2 = j' := by simpa [hp] using hP.head
      exact ⟨p.1, (flip_eq_some hP.nodup_snd).2 (Or.inl (by
        rw [← hpj]; exact List.mem_of_mem_head? hp))⟩
    · by_cases hin : ∃ p ∈ P, p.2 = j'
      · obtain ⟨p, hp, rfl⟩ := hin
        exact ⟨p.1, (flip_eq_some hP.nodup_snd).2 (Or.inl hp)⟩
      · push Not at hin
        exact ⟨i, (flip_eq_some hP.nodup_snd).2 (Or.inr ⟨hin, h⟩)⟩

/-- `pathTo` from a reached unmatched right vertex lists an augmenting path. -/
theorem pathTo_isAugmentingPath (hv : Valid adj mate) {k : ℕ} {j : Fin b}
    (hj : j ∈ (layers adj mate (k + 1)).2) (hfree : mate j = none) :
    IsAugmentingPath adj mate k j (pathTo adj mate k j) :=
  { pathTo_spec hv k j hj with start_free := hfree }

/-- Flipping an augmenting path grows the matching by one edge. -/
theorem card_matched_flip {k : ℕ} {j : Fin b} {P : List (Fin a × Fin b)}
    (hP : IsAugmentingPath adj mate k j P) :
    (matched (flip mate P)).card = (matched mate).card + 1 := by
  rw [matched_flip hP.toAltPath, Finset.card_insert_of_notMem]
  simp [matched, hP.start_free]

end Paths

/-! ## The algorithm -/

/-- One augmentation: find an unmatched right vertex reached by the search and flip the path to
it; `none` if there is none. -/
def augment (mate : Fin b → Option (Fin a)) : Option (Fin b → Option (Fin a)) :=
  let R := (layers adj mate (a + 1)).2
  match (List.finRange b).find? (fun j => decide (mate j = none ∧ j ∈ R)) with
  | none => none
  | some j => some (flip mate (pathTo adj mate a j))

/-- Augment while possible, at most `fuel` times. -/
def maxMatchingAux : ℕ → (Fin b → Option (Fin a)) → Fin b → Option (Fin a)
  | 0, mate => mate
  | fuel + 1, mate =>
      match augment adj mate with
      | none => mate
      | some mate' => maxMatchingAux fuel mate'

/-- A maximum matching, as a partner array: augment from the empty matching. -/
def maxMatching : Fin b → Option (Fin a) := maxMatchingAux adj (b + 1) fun _ => none

section Correctness

variable {adj} {mate : Fin b → Option (Fin a)}

/-- The matched pairs correspond to the matched right vertices. -/
theorem card_pairs (mate : Fin b → Option (Fin a)) : (pairs mate).card = (matched mate).card := by
  refine Finset.card_bij (fun p _ => p.2) (fun p hp => ?_) (fun p hp q hq h => ?_) (fun j hj => ?_)
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [matched, hp]
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rw [h, hq, Option.some.injEq] at hp
    exact Prod.ext hp.symm h
  · simp only [matched, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isSome_iff_exists] at hj
    obtain ⟨i, hi⟩ := hj
    exact ⟨(i, j), by simp [pairs, hi], rfl⟩

/-- A valid partner array describes a matching. -/
theorem isMatching_pairs (hv : Valid adj mate) : IsMatching adj (pairs mate) := by
  refine ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun p hp q hq h => ?_⟩
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hv.edge _ _ hp
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rw [← h] at hq
    exact Prod.ext h (hv.inj _ _ _ hp hq)
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rw [h, hq, Option.some.injEq] at hp
    exact Prod.ext hp.symm h

/-- A successful augmentation keeps a matching and matches one more right vertex. -/
theorem augment_some (hv : Valid adj mate) {mate' : Fin b → Option (Fin a)}
    (h : augment adj mate = some mate') :
    Valid adj mate' ∧ (matched mate').card = (matched mate).card + 1 := by
  simp only [augment] at h
  cases hf : (List.finRange b).find? (fun j =>
      decide (mate j = none ∧ j ∈ (layers adj mate (a + 1)).2)) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some j =>
      rw [hf, Option.some.injEq] at h
      subst h
      have hq := List.find?_some hf
      simp only [decide_eq_true_eq] at hq
      have hP := pathTo_isAugmentingPath hv hq.2 hq.1
      exact ⟨valid_flip hv hP.toAltPath, card_matched_flip hP⟩

/-- A failed augmentation means the search reaches no unmatched right vertex. -/
theorem augment_none (h : augment adj mate = none) :
    ∀ j, mate j = none → j ∉ (layers adj mate (a + 1)).2 := by
  intro j hj hR
  simp only [augment] at h
  cases hf : (List.finRange b).find? (fun j =>
      decide (mate j = none ∧ j ∈ (layers adj mate (a + 1)).2)) with
  | none =>
      simpa [hj, hR] using List.find?_eq_none.1 hf j (List.mem_finRange j)
  | some j' => rw [hf] at h; exact absurd h (by simp)

/-- **Kőnig's certificate.** If the search reaches no unmatched right vertex, no matching is
larger: the unreached left vertices and the reached right vertices cover every edge, and each of
them is matched, to distinct matching edges. -/
theorem card_le_of_no_free (hv : Valid adj mate)
    (h : ∀ j, mate j = none → j ∉ (layers adj mate (a + 1)).2) {M : Finset (Fin a × Fin b)}
    (hM : IsMatching adj M) : M.card ≤ (pairs mate).card := by
  classical
  set Z := (layers adj mate a).1 with hZ
  set R := (layers adj mate (a + 1)).2 with hR
  have hstable : (layers adj mate (a + 1)).1 = Z := layers_fst_stable
  -- the cover
  have hcover : ∀ p ∈ M, p.1 ∈ Z → p.2 ∈ R := by
    intro p hp hpZ
    by_cases hm : mate p.2 = some p.1
    · have hnf : ¬ Free mate p.1 := fun hf => hf p.2 hm
      obtain ⟨j, hjR, hjm⟩ := exists_mate_of_mem_layers hpZ hnf
      rw [hv.inj p.1 p.2 j hm hjm]
      exact layers_snd_mono (Nat.le_succ a) hjR
    · exact mem_layers_succ_snd.2 ⟨p.1, hpZ, hM.edge p hp, hm⟩
  -- every matching is at most the cover
  have h1 : M.card ≤ (Finset.univ \ Z).card + R.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := M) (p := fun p => p.1 ∉ Z)]
    refine Nat.add_le_add (Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_)
      (fun p hp q hq hpq => ?_)) (Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_)
      (fun p hp q hq hpq => ?_))
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
      simp [hp.2]
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      exact hM.left p hp.1 q hq.1 hpq
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, not_not] at hp
      exact Finset.mem_coe.2 (hcover p hp.1 hp.2)
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      exact hM.right p hp.1 q hq.1 hpq
  -- the cover is at most the matching found
  have h2 : (Finset.univ \ Z).card + R.card ≤ (pairs mate).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := pairs mate) (p := fun p => p.1 ∉ Z)]
    refine Nat.add_le_add ((Finset.card_le_card
      (t := ((pairs mate).filter fun p => p.1 ∉ Z).image Prod.fst) fun i hi => ?_).trans
        Finset.card_image_le)
      ((Finset.card_le_card (t := ((pairs mate).filter fun p => ¬ p.1 ∉ Z).image Prod.snd)
        fun j hj => ?_).trans Finset.card_image_le)
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      have hnf : ¬ Free mate i := fun hf =>
        hi (layers_fst_mono (Nat.zero_le a) (mem_layers_zero_fst.2 hf))
      simp only [Free, not_forall, not_not] at hnf
      obtain ⟨j, hj⟩ := hnf
      exact Finset.mem_image.2 ⟨(i, j), by simp [pairs, hj, hi], rfl⟩
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 fun hn => h j hn hj
      have hiZ : i ∈ Z := by
        rw [← hstable]; exact mem_layers_succ_fst.2 (Or.inr ⟨j, hj, hi⟩)
      exact Finset.mem_image.2 ⟨(i, j), by simp [pairs, hi, hiZ], rfl⟩
  exact h1.trans h2

/-- With more fuel than unmatched right vertices, the loop ends with a maximum matching. -/
theorem maxMatchingAux_spec : ∀ (fuel : ℕ) (mate : Fin b → Option (Fin a)), Valid adj mate →
    b < (matched mate).card + fuel →
    Valid adj (maxMatchingAux adj fuel mate) ∧
      ∀ M, IsMatching adj M → M.card ≤ (pairs (maxMatchingAux adj fuel mate)).card
  | 0, mate, _, hb => by
      have : (matched mate).card ≤ b := by
        simpa using Finset.card_le_univ (matched mate)
      omega
  | fuel + 1, mate, hv, hb => by
      simp only [maxMatchingAux]
      cases ha : augment adj mate with
      | none => exact ⟨hv, fun M hM => card_le_of_no_free hv (augment_none ha) hM⟩
      | some mate' =>
          obtain ⟨hv', hc⟩ := augment_some hv ha
          exact maxMatchingAux_spec fuel mate' hv' (by omega)

/-- The result is a matching. -/
theorem isMatching_maxMatching : IsMatching adj (pairs (maxMatching adj)) :=
  isMatching_pairs (maxMatchingAux_spec (b + 1) _ ⟨by simp, by simp⟩ (by omega)).1

/-- **Correctness.** No matching is larger than the result. -/
theorem card_le_maxMatching {M : Finset (Fin a × Fin b)} (hM : IsMatching adj M) :
    M.card ≤ (pairs (maxMatching adj)).card :=
  (maxMatchingAux_spec (b + 1) _ ⟨by simp, by simp⟩ (by omega)).2 M hM

end Correctness

/-! ## Hopcroft–Karp phases -/

/-- The partner of a left vertex, if it is matched. -/
def partnerOf (mate : Fin b → Option (Fin a)) (i : Fin a) : Option (Fin b) :=
  (List.finRange b).find? fun j' => decide (mate j' = some i)

/-- Add `j` to a set of dead right vertices. -/
def markDead (dead : Fin b → Bool) (j : Fin b) : Fin b → Bool :=
  fun x => dead x || decide (x = j)

/-- Try the candidate predecessors `is` of `j` in order: for the first `i` with `ok i`, if `i` is
unmatched the path is `[(i, j)]`, otherwise continue from its partner with `search`; a failed
search leaves its dead vertices marked for the next candidate. If every candidate fails, `j` is
marked dead too. -/
def tryPreds (ok : Fin a → Bool) (partner : Fin a → Option (Fin b))
    (search : Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool))
    (j : Fin b) : List (Fin a) → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)
  | [], dead => (none, markDead dead j)
  | i :: is, dead =>
      if ok i then
        match partner i with
        | none => (some [(i, j)], dead)
        | some j' =>
            match search j' dead with
            | (some P, dead') => (some ((i, j) :: P), dead')
            | (none, dead') => tryPreds ok partner search j is dead'
      else tryPreds ok partner search j is dead

/-- `pathTo` restricted to unused vertices, as a depth-first search over the layers with the
pruning of Hopcroft and Karp: from a reached right vertex `j` that is not dead, descend to the
round where `j` is first reached and try each predecessor `i` of the round before that is not in
`usedL`, continuing from the partner of `i`. A right vertex from which the search fails is marked
dead, so each right vertex fails at most once per phase. Returns the path found, if any, and the
dead set. -/
def searchPath (mate : Fin b → Option (Fin a)) (usedL : Fin a → Bool) :
    ℕ → Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)
  | 0, j, dead =>
      let Z := (layers adj mate 0).1
      if dead j then (none, dead)
      else
        tryPreds (fun i => decide (i ∈ Z ∧ j ∈ adj i ∧ mate j ≠ some i ∧ usedL i = false))
          (partnerOf mate) (fun _ d => (none, d)) j (List.finRange a) dead
  | k + 1, j, dead =>
      let L := layers adj mate (k + 1)
      if dead j then (none, dead)
      else if j ∈ L.2 then searchPath mate usedL k j dead
      else
        tryPreds (fun i => decide (i ∈ L.1 ∧ j ∈ adj i ∧ mate j ≠ some i ∧ usedL i = false))
          (partnerOf mate) (fun j' d => searchPath mate usedL k j' d) j (List.finRange a) dead

section Search

variable {adj} {mate : Fin b → Option (Fin a)}

theorem markDead_eq_false_iff {dead : Fin b → Bool} {j x : Fin b} :
    markDead dead j x = false ↔ dead x = false ∧ x ≠ j := by
  simp [markDead]

theorem partnerOf_eq_some {i : Fin a} {j : Fin b} (h : partnerOf mate i = some j) :
    mate j = some i := by
  simpa using List.find?_some h

theorem partnerOf_eq_none {i : Fin a} (h : partnerOf mate i = none) : Free mate i := by
  intro j hj
  simpa [hj] using List.find?_eq_none.1 h j (List.mem_finRange j)

/-- The dead set only grows. -/
theorem tryPreds_mono {ok : Fin a → Bool} {partner : Fin a → Option (Fin b)}
    {search : Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)}
    (hs : ∀ j' d x, d x = true → (search j' d).2 x = true) (j : Fin b) :
    ∀ (is : List (Fin a)) (dead : Fin b → Bool) (x : Fin b), dead x = true →
      (tryPreds ok partner search j is dead).2 x = true
  | [], dead, x, hx => by simp [tryPreds, markDead, hx]
  | i :: is, dead, x, hx => by
      simp only [tryPreds]
      split_ifs
      · cases hp : partner i with
        | none => exact hx
        | some j' =>
            dsimp only
            have h1 := hs j' dead x hx
            cases hsr : search j' dead with
            | mk r d =>
                rw [hsr] at h1
                cases r with
                | some P => exact h1
                | none => exact tryPreds_mono hs j is d x h1
      · exact tryPreds_mono hs j is dead x hx

/-- What `tryPreds` returns comes from one candidate `i` with `ok i`, searched with a dead set
that contains the initial one. -/
theorem tryPreds_some {ok : Fin a → Bool} {partner : Fin a → Option (Fin b)}
    {search : Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)}
    (hs : ∀ j' d x, d x = true → (search j' d).2 x = true) (j : Fin b) :
    ∀ (is : List (Fin a)) (dead : Fin b → Bool) (P : List (Fin a × Fin b)),
      (tryPreds ok partner search j is dead).1 = some P →
      ∃ i ∈ is, ok i = true ∧ ∃ dead₀ : Fin b → Bool, (∀ x, dead x = true → dead₀ x = true) ∧
        ((partner i = none ∧ P = [(i, j)]) ∨
          ∃ j' P', partner i = some j' ∧ (search j' dead₀).1 = some P' ∧ P = (i, j) :: P')
  | [], dead, P, h => by simp [tryPreds] at h
  | i :: is, dead, P, h => by
      simp only [tryPreds] at h
      split_ifs at h with hok
      · split at h
        · rename_i hp
          simp only [Option.some.injEq] at h
          exact ⟨i, List.mem_cons_self, hok, dead, fun _ hx => hx, Or.inl ⟨hp, h.symm⟩⟩
        · rename_i j' hp
          split at h
          · rename_i P' dead' hsr
            simp only [Option.some.injEq] at h
            exact ⟨i, List.mem_cons_self, hok, dead, fun _ hx => hx,
              Or.inr ⟨j', P', hp, by rw [hsr], h.symm⟩⟩
          · rename_i dead' hsr
            obtain ⟨i₁, hi₁, hok₁, d₀, hd₀, hcase⟩ := tryPreds_some hs j is dead' P h
            refine ⟨i₁, List.mem_cons_of_mem _ hi₁, hok₁, d₀, fun x hx => hd₀ x ?_, hcase⟩
            have := hs j' dead x hx
            rwa [hsr] at this
      · obtain ⟨i₁, hi₁, hok₁, d₀, hd₀, hcase⟩ := tryPreds_some hs j is dead P h
        exact ⟨i₁, List.mem_cons_of_mem _ hi₁, hok₁, d₀, hd₀, hcase⟩

/-- `tryPreds` finds a path when some candidate passes `ok` and every such candidate is unmatched
or has a partner from which `search` succeeds with the initial dead set (the dead set does not
change until the first candidate that passes `ok`). -/
theorem tryPreds_isSome {ok : Fin a → Bool} {partner : Fin a → Option (Fin b)}
    {search : Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)}
    (j : Fin b) (dead : Fin b → Bool) : ∀ (is : List (Fin a)), (∃ i ∈ is, ok i = true) →
      (∀ i ∈ is, ok i = true → ∀ j', partner i = some j' → (search j' dead).1.isSome) →
      (tryPreds ok partner search j is dead).1.isSome
  | [], h, _ => by simp at h
  | i :: is, ⟨i₀, hi₀, hok₀⟩, hall => by
      simp only [tryPreds]
      by_cases hok : ok i = true
      · simp only [hok, ↓reduceIte]
        cases hp : partner i with
        | none => rfl
        | some j' =>
            have := hall i List.mem_cons_self hok j' hp
            obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 this
            simp only
            cases hsr : search j' dead with
            | mk r d =>
                rw [hsr] at hP
                simp only at hP
                subst hP
                rfl
      · simp only [Bool.not_eq_true] at hok
        simp only [hok, Bool.false_eq_true, ↓reduceIte]
        refine tryPreds_isSome j dead is ?_ fun i' hi' => hall i' (List.mem_cons_of_mem _ hi')
        rcases List.mem_cons.1 hi₀ with rfl | h
        · rw [hok] at hok₀; exact absurd hok₀ (by simp)
        · exact ⟨i₀, h, hok₀⟩

/-- The dead set of `searchPath` only grows. -/
theorem searchPath_mono (usedL : Fin a → Bool) : ∀ (k : ℕ) (j : Fin b) (dead : Fin b → Bool)
    (x : Fin b), dead x = true → (searchPath adj mate usedL k j dead).2 x = true
  | 0, j, dead, x, hx => by
      simp only [searchPath]
      split_ifs
      · exact hx
      · exact tryPreds_mono (fun _ d x hx => hx) j _ dead x hx
  | k + 1, j, dead, x, hx => by
      simp only [searchPath]
      split_ifs
      · exact hx
      · exact searchPath_mono usedL k j dead x hx
      · exact tryPreds_mono (fun j' d x hx => searchPath_mono usedL k j' d x hx) j _ dead x hx

/-- What `searchPath` finds is an alternating path through vertices that were neither used nor
dead. -/
theorem searchPath_spec (hv : Valid adj mate) (usedL : Fin a → Bool) :
    ∀ (k : ℕ) (j : Fin b) (dead : Fin b → Bool) (P : List (Fin a × Fin b)),
      j ∈ (layers adj mate (k + 1)).2 → (searchPath adj mate usedL k j dead).1 = some P →
      AltPath adj mate k j P ∧ ∀ p ∈ P, usedL p.1 = false ∧ dead p.2 = false
  | 0, j, dead, P, hj, hP => by
      simp only [searchPath] at hP
      split_ifs at hP with hu
      obtain ⟨i, -, hok, d₀, -, hcase⟩ := tryPreds_some (fun _ d x hx => hx) j _ dead P hP
      simp only [decide_eq_true_eq] at hok
      obtain ⟨hiZ, hiadj, him, hiu⟩ := hok
      rcases hcase with ⟨-, rfl⟩ | ⟨j', P', -, hsr, -⟩
      · refine ⟨⟨rfl, ?_, ?_, by simp, by simp, List.isChain_singleton _, ?_⟩, ?_⟩
        · simp only [List.mem_singleton]; rintro p rfl; exact ⟨hiadj, him⟩
        · simp only [List.mem_singleton]; rintro p rfl; exact ⟨hiZ, hj⟩
        · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq]
          rintro p rfl; exact mem_layers_zero_fst.1 hiZ
        · simp only [List.mem_singleton]; rintro p rfl; exact ⟨hiu, by simpa using hu⟩
      · simp at hsr
  | k + 1, j, dead, P, hj, hP => by
      simp only [searchPath] at hP
      split_ifs at hP with hu hjk
      · obtain ⟨h1, h2⟩ := searchPath_spec hv usedL k j dead P hjk hP
        exact ⟨h1.mono, h2⟩
      · obtain ⟨i, -, hok, d₀, hd₀, hcase⟩ := tryPreds_some
          (fun j' d x hx => searchPath_mono usedL k j' d x hx) j _ dead P hP
        simp only [decide_eq_true_eq] at hok
        obtain ⟨hiZ, hiadj, him, hiu⟩ := hok
        have hnot : i ∉ (layers adj mate k).1 := fun h =>
          hjk (mem_layers_succ_snd.2 ⟨i, h, hiadj, him⟩)
        have hnf : ¬ Free mate i := fun h =>
          hnot (layers_fst_mono (Nat.zero_le k) (mem_layers_zero_fst.2 h))
        obtain ⟨j'', hj''R, hj''m⟩ := exists_mate_of_mem_layers hiZ hnf
        rcases hcase with ⟨hp, -⟩ | ⟨j', P', hp, hsr, rfl⟩
        · exact absurd (partnerOf_eq_none hp) hnf
        have hj'm : mate j' = some i := partnerOf_eq_some hp
        have hj'eq : j' = j'' := hv.inj i j' j'' hj'm hj''m
        subst hj'eq
        obtain ⟨⟨hh, he, hl, hn1, hn2, hc, hlast⟩, hused⟩ :=
          searchPath_spec hv usedL k j' d₀ P' hj''R hsr
        have hne : P' ≠ [] := by
          intro h; rw [h] at hh; simp at hh
        refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨hiadj, him⟩
          · exact he p hp
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨hiZ, hj⟩
          · exact ⟨layers_fst_mono (Nat.le_succ k) (hl p hp).1,
              layers_snd_mono (Nat.le_succ _) (hl p hp).2⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hn1⟩
          obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hmem
          have := (hl p hp).1
          rw [hpi] at this
          exact hnot this
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hn2⟩
          obtain ⟨p, hp, hpj⟩ := List.mem_map.1 hmem
          have := (hl p hp).2
          rw [hpj] at this
          exact hjk this
        · rw [List.isChain_cons]
          refine ⟨fun q hq => ?_, hc⟩
          rw [Option.mem_def] at hq
          have : q.2 = j' := by simpa [hq] using hh
          simp only [this, hj'm]
        · intro p hp
          rw [List.getLast?_cons, Option.mem_def] at hp
          obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (List.getLast?_eq_none_iff.not.2 hne)
          rw [hx] at hp
          simp only [Option.getD_some, Option.some.injEq] at hp
          exact hlast p (by rw [Option.mem_def, hx, hp])
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨hiu, by simpa using hu⟩
          · obtain ⟨h1, h2⟩ := hused p hp
            refine ⟨h1, ?_⟩
            cases hdp : dead p.2
            · rfl
            · exact absurd (hd₀ _ hdp) (by rw [h2]; simp)

/-- With no vertex used or dead, `searchPath` finds a path from every reached right vertex. -/
theorem searchPath_isSome (hv : Valid adj mate) : ∀ (k : ℕ) (j : Fin b),
    j ∈ (layers adj mate (k + 1)).2 →
      (searchPath adj mate (fun _ => false) k j (fun _ => false)).1.isSome
  | 0, j, hj => by
      obtain ⟨i, hi, h1, h2⟩ := mem_layers_succ_snd.1 hj
      simp only [searchPath, Bool.false_eq_true, ite_false]
      refine tryPreds_isSome j _ _ ⟨i, List.mem_finRange i, by simp [hi, h1, h2]⟩ ?_
      intro i' _ hok j' hp
      simp only [decide_eq_true_eq] at hok
      exact absurd (partnerOf_eq_some hp) (mem_layers_zero_fst.1 hok.1 j')
  | k + 1, j, hj => by
      simp only [searchPath, Bool.false_eq_true, ite_false]
      split_ifs with hjk
      · exact searchPath_isSome hv k j hjk
      · obtain ⟨i, hi, h1, h2⟩ := mem_layers_succ_snd.1 hj
        refine tryPreds_isSome j _ _ ⟨i, List.mem_finRange i, by simp [hi, h1, h2]⟩ ?_
        intro i' _ hok j' hp
        simp only [decide_eq_true_eq] at hok
        have hj'm := partnerOf_eq_some hp
        have hnf : ¬ Free mate i' := fun hfr => hfr j' hj'm
        obtain ⟨j'', hj''R, hj''m⟩ := exists_mate_of_mem_layers hok.1 hnf
        have hj'eq : j' = j'' := hv.inj i' j' j'' hj'm hj''m
        subst hj'eq
        exact searchPath_isSome hv k j' hj''R

end Search

/-- Add the left vertices of a path to a used set. -/
def markL (used : Fin a → Bool) (P : List (Fin a × Fin b)) : Fin a → Bool :=
  fun i => used i || decide (i ∈ P.map Prod.fst)

/-- Add the right vertices of a path to a used set. -/
def markR (used : Fin b → Bool) (P : List (Fin a × Fin b)) : Fin b → Bool :=
  fun j => used j || decide (j ∈ P.map Prod.snd)

/-- Search from each listed right vertex in turn through the vertices not yet used, collecting the
paths found; each path's vertices become used, and right vertices from which a search failed stay
dead. -/
def phaseAux (mate : Fin b → Option (Fin a)) (k : ℕ) :
    List (Fin b) → (Fin a → Bool) → (Fin b → Bool) → List (List (Fin a × Fin b))
  | [], _, _ => []
  | j :: js, usedL, usedR =>
      match searchPath adj mate usedL k j usedR with
      | (none, dead) => phaseAux mate k js usedL dead
      | (some P, dead) => P :: phaseAux mate k js (markL usedL P) (markR dead P)

/-- The earliest round `d` such that round `d + 1` of the search reaches an unmatched right
vertex, if any round does. -/
def firstFreeRound (mate : Fin b → Option (Fin a)) : Option ℕ :=
  (List.range (a + 1)).find? fun k => decide (∃ j, mate j = none ∧ j ∈ (layers adj mate (k + 1)).2)

/-- One Hopcroft–Karp phase: from the layers of one search, vertex-disjoint augmenting paths from
the unmatched right vertices reached in the earliest round that reaches any, one attempt from
each. -/
def phase (mate : Fin b → Option (Fin a)) : List (List (Fin a × Fin b)) :=
  match firstFreeRound adj mate with
  | none => []
  | some d =>
      let R := (layers adj mate (d + 1)).2
      phaseAux adj mate d ((List.finRange b).filter fun j => decide (mate j = none ∧ j ∈ R))
        (fun _ => false) (fun _ => false)

/-- Flip all the paths of a phase at once; `none` if the phase found none. -/
def hkStep (mate : Fin b → Option (Fin a)) : Option (Fin b → Option (Fin a)) :=
  let Ps := phase adj mate
  if Ps.isEmpty then none else some (flip mate Ps.flatten)

/-- Run phases while they find paths, at most `fuel` times. -/
def hopcroftKarpAux : ℕ → (Fin b → Option (Fin a)) → Fin b → Option (Fin a)
  | 0, mate => mate
  | fuel + 1, mate =>
      match hkStep adj mate with
      | none => mate
      | some mate' => hopcroftKarpAux fuel mate'

/-- **Hopcroft–Karp.** A maximum matching by phases, from the empty matching. -/
def hopcroftKarp : Fin b → Option (Fin a) := hopcroftKarpAux adj (b + 1) fun _ => none

section Phases

variable {adj} {mate : Fin b → Option (Fin a)}

theorem markL_eq_false_iff {used : Fin a → Bool} {P : List (Fin a × Fin b)} {i : Fin a} :
    markL used P i = false ↔ used i = false ∧ i ∉ P.map Prod.fst := by
  simp [markL]

theorem markR_eq_false_iff {used : Fin b → Bool} {P : List (Fin a × Fin b)} {j : Fin b} :
    markR used P j = false ↔ used j = false ∧ j ∉ P.map Prod.snd := by
  simp [markR]

/-- `firstFreeRound` is the earliest round `d` (at most `a`) such that round `d + 1` reaches an
unmatched right vertex. -/
theorem firstFreeRound_eq_some {d : ℕ} : firstFreeRound adj mate = some d ↔
    d ≤ a ∧ (∃ j, mate j = none ∧ j ∈ (layers adj mate (d + 1)).2) ∧
      ∀ k < d, ∀ j, mate j = none → j ∉ (layers adj mate (k + 1)).2 := by
  simp only [firstFreeRound, List.find?_range_eq_some, decide_eq_true_eq, List.mem_range,
    Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega, h3⟩

/-- `firstFreeRound` is `none` exactly when the search reaches no unmatched right vertex. -/
theorem firstFreeRound_eq_none : firstFreeRound adj mate = none ↔
    ∀ j, mate j = none → j ∉ (layers adj mate (a + 1)).2 := by
  simp only [firstFreeRound, List.find?_eq_none, List.mem_range, decide_eq_true_eq, not_exists,
    not_and]
  constructor
  · intro h j hj hR; exact h a (Nat.lt_succ_self a) j hj hR
  · intro h k hk j hj hR; exact h j hj (layers_snd_mono (by omega) hR)

/-- The paths of a phase are augmenting paths, pairwise vertex-disjoint, through vertices not
initially used. -/
theorem phaseAux_spec (hv : Valid adj mate) (k : ℕ) : ∀ (js : List (Fin b))
    (usedL : Fin a → Bool) (usedR : Fin b → Bool),
    (∀ j ∈ js, mate j = none ∧ j ∈ (layers adj mate (k + 1)).2) →
    (∀ P ∈ phaseAux adj mate k js usedL usedR, ∃ j, IsAugmentingPath adj mate k j P) ∧
      ((phaseAux adj mate k js usedL usedR).flatten.map Prod.fst).Nodup ∧
      ((phaseAux adj mate k js usedL usedR).flatten.map Prod.snd).Nodup ∧
      ∀ p ∈ (phaseAux adj mate k js usedL usedR).flatten, usedL p.1 = false ∧ usedR p.2 = false
  | [], _, _, _ => by simp [phaseAux]
  | j :: js, usedL, usedR, hjs => by
      have hjs' : ∀ j ∈ js, mate j = none ∧ j ∈ (layers adj mate (k + 1)).2 :=
        fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')
      -- vertices unused after the search were unused before it
      have hback : ∀ (d : Fin b → Bool), (∀ x, usedR x = true → d x = true) →
          ∀ x, d x = false → usedR x = false := by
        intro d hd x hx
        cases h : usedR x
        · rfl
        · rw [hd x h] at hx; exact absurd hx (by simp)
      have hmono := searchPath_mono (adj := adj) (mate := mate) usedL k j usedR
      cases hs : searchPath adj mate usedL k j usedR with
      | mk r dead =>
      cases r with
      | none =>
          simp only [phaseAux, hs]
          obtain ⟨h1, h2, h3, h4⟩ := phaseAux_spec hv k js usedL dead hjs'
          refine ⟨h1, h2, h3, fun p hp => ⟨(h4 p hp).1, hback dead ?_ _ (h4 p hp).2⟩⟩
          intro x hx; have := hmono x hx; rwa [hs] at this
      | some P =>
          simp only [phaseAux, hs]
          obtain ⟨hj0, hjR⟩ := hjs j List.mem_cons_self
          obtain ⟨hP, hPu⟩ := searchPath_spec hv usedL k j usedR P hjR (by rw [hs])
          obtain ⟨h1, h2, h3, h4⟩ := phaseAux_spec hv k js (markL usedL P) (markR dead P) hjs'
          refine ⟨fun Q hQ => ?_, ?_, ?_, fun p hp => ?_⟩
          · rcases List.mem_cons.1 hQ with rfl | hQ
            · exact ⟨j, { hP with start_free := hj0 }⟩
            · exact h1 Q hQ
          · rw [List.flatten_cons, List.map_append, List.nodup_append]
            refine ⟨hP.nodup_fst, h2, fun x hx y hy hxy => ?_⟩
            obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
            have := (h4 q hq).1
            simp only [markL, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
            exact this.2 (hxy ▸ hx)
          · rw [List.flatten_cons, List.map_append, List.nodup_append]
            refine ⟨hP.nodup_snd, h3, fun x hx y hy hxy => ?_⟩
            obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
            have := (h4 q hq).2
            simp only [markR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
            exact this.2 (hxy ▸ hx)
          · rw [List.flatten_cons, List.mem_append] at hp
            rcases hp with hp | hp
            · exact hPu p hp
            · have h := h4 p hp
              simp only [markL, markR, Bool.or_eq_false_iff] at h
              refine ⟨h.1.1, hback dead ?_ _ h.2.1⟩
              intro x hx; have := hmono x hx; rwa [hs] at this

/-- Flipping vertex-disjoint alternating paths at once gives a matching. -/
theorem valid_flip_flatten (hv : Valid adj mate) {k : ℕ} {Ps : List (List (Fin a × Fin b))}
    (hPs : ∀ P ∈ Ps, ∃ j, AltPath adj mate k j P) (h1 : (Ps.flatten.map Prod.fst).Nodup)
    (h2 : (Ps.flatten.map Prod.snd).Nodup) : Valid adj (flip mate Ps.flatten) := by
  refine ⟨fun i j' h => ?_, fun i j₁ j₂ h₁ h₂ => ?_⟩
  · rcases (flip_eq_some h2).1 h with h | ⟨-, h⟩
    · obtain ⟨P, hP, hp⟩ := List.mem_flatten.1 h
      obtain ⟨j, hPj⟩ := hPs P hP
      exact (hPj.edge _ hp).1
    · exact hv.edge i j' h
  · have key : ∀ j₁ j₂, (i, j₁) ∈ Ps.flatten → (∀ p ∈ Ps.flatten, p.2 ≠ j₂) →
        mate j₂ = some i → False := by
      intro j₁ j₂ hp hall hm
      obtain ⟨P, hP, hp⟩ := List.mem_flatten.1 hp
      obtain ⟨j, hPj⟩ := hPs P hP
      rcases last_or_succ hPj.chain _ hp with hl | ⟨q, hq, hqm⟩
      · exact hPj.last _ hl j₂ hm
      · exact hall q (List.mem_flatten.2 ⟨P, hP, hq⟩) (hv.inj i q.2 j₂ hqm hm)
    rcases (flip_eq_some h2).1 h₁ with h₁ | ⟨hall₁, h₁⟩ <;>
      rcases (flip_eq_some h2).1 h₂ with h₂ | ⟨hall₂, h₂⟩
    · have := List.inj_on_of_nodup_map h1 h₁ h₂ rfl
      simpa using congrArg Prod.snd this
    · exact (key _ _ h₁ hall₂ h₂).elim
    · exact (key _ _ h₂ hall₁ h₁).elim
    · exact hv.inj i j₁ j₂ h₁ h₂

/-- Flipping a nonempty set of vertex-disjoint augmenting paths matches at least one more right
vertex: the right vertices matched before stay matched, and so does the start of the first
path. -/
theorem card_matched_flip_flatten {k : ℕ} {Ps : List (List (Fin a × Fin b))}
    (hPs : ∀ P ∈ Ps, ∃ j, IsAugmentingPath adj mate k j P) (h2 : (Ps.flatten.map Prod.snd).Nodup)
    (hne : Ps ≠ []) : (matched mate).card + 1 ≤ (matched (flip mate Ps.flatten)).card := by
  obtain ⟨P₀, Ps', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨j₀, hP₀⟩ := hPs P₀ List.mem_cons_self
  obtain ⟨p₀, hp₀⟩ : ∃ p, P₀.head? = some p := by
    cases hh : P₀.head? with
    | none => have := hP₀.head; rw [hh] at this; simp at this
    | some p => exact ⟨p, rfl⟩
  have hpj : p₀.2 = j₀ := by simpa [hp₀] using hP₀.head
  have hsub : insert j₀ (matched mate) ⊆ matched (flip mate (P₀ :: Ps').flatten) := by
    intro j' hj'
    simp only [matched, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isSome_iff_exists] at hj' ⊢
    rcases hj' with rfl | ⟨i, hi⟩
    · refine ⟨p₀.1, (flip_eq_some h2).2 (Or.inl ?_)⟩
      rw [← hpj]
      exact List.mem_flatten.2 ⟨P₀, List.mem_cons_self, List.mem_of_mem_head? hp₀⟩
    · by_cases hin : ∃ p ∈ (P₀ :: Ps').flatten, p.2 = j'
      · obtain ⟨p, hp, rfl⟩ := hin
        exact ⟨p.1, (flip_eq_some h2).2 (Or.inl hp)⟩
      · push Not at hin
        exact ⟨i, (flip_eq_some h2).2 (Or.inr ⟨hin, hi⟩)⟩
  have hnot : j₀ ∉ matched mate := by simp [matched, hP₀.start_free]
  calc (matched mate).card + 1 = (insert j₀ (matched mate)).card :=
        (Finset.card_insert_of_notMem hnot).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The candidates of a phase: unmatched right vertices reached by round `d + 1`. -/
private theorem mem_candidates {d : ℕ} {j : Fin b} :
    j ∈ (List.finRange b).filter (fun j => decide (mate j = none ∧
      j ∈ (layers adj mate (d + 1)).2)) ↔ mate j = none ∧ j ∈ (layers adj mate (d + 1)).2 := by
  simp

/-- The first candidate always yields a path, so a phase finds a path whenever the search reaches
an unmatched right vertex. -/
theorem phase_ne_nil (hv : Valid adj mate) {j : Fin b} (hj : mate j = none)
    (hR : j ∈ (layers adj mate (a + 1)).2) : phase adj mate ≠ [] := by
  obtain ⟨d, hd⟩ : ∃ d, firstFreeRound adj mate = some d := by
    cases hf : firstFreeRound adj mate with
    | none => exact absurd hR (firstFreeRound_eq_none.1 hf j hj)
    | some d => exact ⟨d, rfl⟩
  obtain ⟨-, ⟨j₁, hj₁, hj₁R⟩, -⟩ := firstFreeRound_eq_some.1 hd
  simp only [phase, hd]
  set js := (List.finRange b).filter fun j => decide (mate j = none ∧
    j ∈ (layers adj mate (d + 1)).2)
  have hmem : j₁ ∈ js := mem_candidates.2 ⟨hj₁, hj₁R⟩
  obtain ⟨j₀, js', hjs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hj₀ : j₀ ∈ js := hjs ▸ List.mem_cons_self
  have hj₀R : j₀ ∈ (layers adj mate (d + 1)).2 := (mem_candidates.1 hj₀).2
  rw [hjs]
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 (searchPath_isSome hv d j₀ hj₀R)
  simp only [phaseAux]
  cases hs : searchPath adj mate (fun _ => false) d j₀ (fun _ => false) with
  | mk r dead =>
      rw [hs] at hP
      simp only at hP
      subst hP
      simp

/-- A phase that finds paths keeps a matching and matches at least one more right vertex. -/
theorem hkStep_some (hv : Valid adj mate) {mate' : Fin b → Option (Fin a)}
    (h : hkStep adj mate = some mate') :
    Valid adj mate' ∧ (matched mate).card + 1 ≤ (matched mate').card := by
  simp only [hkStep] at h
  split_ifs at h with hemp
  rw [Option.some.injEq] at h
  subst h
  have hne : phase adj mate ≠ [] := by simpa [List.isEmpty_iff] using hemp
  cases hf : firstFreeRound adj mate with
  | none => exact absurd (by simp [phase, hf]) hne
  | some d =>
      -- the paths come from `phaseAux` at the earliest round `d`
      have hph : phase adj mate = phaseAux adj mate d ((List.finRange b).filter fun j =>
          decide (mate j = none ∧ j ∈ (layers adj mate (d + 1)).2))
          (fun _ => false) (fun _ => false) := by
        simp only [phase, hf]
      rw [hph] at hne ⊢
      obtain ⟨h1, h2, h3, -⟩ := phaseAux_spec hv d _ (fun _ => false) (fun _ => false)
        (fun j hj => mem_candidates.1 hj)
      refine ⟨valid_flip_flatten (k := d) hv (fun P hP => ?_) h2 h3,
        card_matched_flip_flatten h1 h3 hne⟩
      obtain ⟨j, hPj⟩ := h1 P hP
      exact ⟨j, hPj.toAltPath⟩

/-- A phase that finds no path means the search reaches no unmatched right vertex. -/
theorem hkStep_none (hv : Valid adj mate) (h : hkStep adj mate = none) :
    ∀ j, mate j = none → j ∉ (layers adj mate (a + 1)).2 := by
  intro j hj hR
  simp only [hkStep] at h
  split_ifs at h with hemp
  · exact phase_ne_nil hv hj hR (List.isEmpty_iff.1 hemp)

/-- With more fuel than unmatched right vertices, the phases end with a maximum matching. -/
theorem hopcroftKarpAux_spec : ∀ (fuel : ℕ) (mate : Fin b → Option (Fin a)), Valid adj mate →
    b < (matched mate).card + fuel →
    Valid adj (hopcroftKarpAux adj fuel mate) ∧
      ∀ M, IsMatching adj M → M.card ≤ (pairs (hopcroftKarpAux adj fuel mate)).card
  | 0, mate, _, hb => by
      have : (matched mate).card ≤ b := by
        simpa using Finset.card_le_univ (matched mate)
      omega
  | fuel + 1, mate, hv, hb => by
      simp only [hopcroftKarpAux]
      cases hs : hkStep adj mate with
      | none => exact ⟨hv, fun M hM => card_le_of_no_free hv (hkStep_none hv hs) hM⟩
      | some mate' =>
          obtain ⟨hv', hc⟩ := hkStep_some hv hs
          exact hopcroftKarpAux_spec fuel mate' hv' (by omega)

/-- The result of Hopcroft–Karp is a matching. -/
theorem isMatching_hopcroftKarp : IsMatching adj (pairs (hopcroftKarp adj)) :=
  isMatching_pairs (hopcroftKarpAux_spec (b + 1) _ ⟨by simp, by simp⟩ (by omega)).1

/-- **Correctness of Hopcroft–Karp.** No matching is larger than the result. -/
theorem card_le_hopcroftKarp {M : Finset (Fin a × Fin b)} (hM : IsMatching adj M) :
    M.card ≤ (pairs (hopcroftKarp adj)).card :=
  (hopcroftKarpAux_spec (b + 1) _ ⟨by simp, by simp⟩ (by omega)).2 M hM

end Phases

/-! ## Phases use shortest augmenting paths -/

section Shortest

variable {adj} {mate : Fin b → Option (Fin a)}

/-- An alternating chain of `L` pairs that ends at an unmatched left vertex reaches its first right
vertex within `L` rounds of the layered search: from the unmatched end, each pair advances one
round. -/
theorem mem_layers_length : ∀ (P : List (Fin a × Fin b)),
    (∀ p ∈ P, p.2 ∈ adj p.1 ∧ mate p.2 ≠ some p.1) →
    List.IsChain (fun p q => mate q.2 = some p.1) P → (∀ p ∈ P.getLast?, Free mate p.1) →
    ∀ p ∈ P.head?, p.2 ∈ (layers adj mate P.length).2
  | [], _, _, _ => by simp
  | [(i, j)], he, _, hl => by
      intro p hp
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp
      subst hp
      have hi : i ∈ (layers adj mate 0).1 := mem_layers_zero_fst.2 (hl (i, j) (by simp))
      exact mem_layers_succ_snd.2 ⟨i, hi, he (i, j) (by simp)⟩
  | (i, j) :: q :: P, he, hc, hl => by
      intro p hp
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp
      subst hp
      have ih := mem_layers_length (q :: P) (fun p hp => he p (List.mem_cons_of_mem _ hp))
        (List.isChain_cons_cons.1 hc).2 (by rwa [List.getLast?_cons_cons] at hl) q (by simp)
      have hm : mate q.2 = some i := (List.isChain_cons_cons.1 hc).1
      have hi : i ∈ (layers adj mate (q :: P).length).1 :=
        mem_layers_succ_fst.2 (Or.inr ⟨q.2, ih, hm⟩)
      exact mem_layers_succ_snd.2 ⟨i, hi, he (i, j) (by simp)⟩

/-- **No augmenting path is shorter than a phase's.** If `firstFreeRound` is `d`, every augmenting
path has at least `d + 1` pairs. -/
theorem le_length_of_isAugmentingPath {d k : ℕ} (hd : firstFreeRound adj mate = some d)
    {j : Fin b} {P : List (Fin a × Fin b)} (hP : IsAugmentingPath adj mate k j P) :
    d + 1 ≤ P.length := by
  obtain ⟨-, -, hmin⟩ := firstFreeRound_eq_some.1 hd
  cases P with
  | nil => simpa using hP.head
  | cons p P =>
      have hpj : p.2 = j := by simpa using hP.head
      have hR := mem_layers_length (p :: P) hP.edge hP.chain hP.last p (by simp)
      rw [hpj] at hR
      by_contra hlt
      exact hmin P.length (by simp only [List.length_cons] at hlt; omega) j hP.start_free hR

/-- What `searchPath` at level `k` finds has at most `k + 1` pairs. -/
theorem searchPath_length_le (usedL : Fin a → Bool) : ∀ (k : ℕ) (j : Fin b)
    (dead : Fin b → Bool) (P : List (Fin a × Fin b)),
    (searchPath adj mate usedL k j dead).1 = some P → P.length ≤ k + 1
  | 0, j, dead, P, hP => by
      simp only [searchPath] at hP
      split_ifs at hP
      obtain ⟨i, -, -, d₀, -, hcase⟩ := tryPreds_some (fun _ d x hx => hx) j _ dead P hP
      rcases hcase with ⟨-, rfl⟩ | ⟨j', P', -, hsr, -⟩
      · simp
      · simp at hsr
  | k + 1, j, dead, P, hP => by
      simp only [searchPath] at hP
      split_ifs at hP
      · exact (searchPath_length_le usedL k j dead P hP).trans (Nat.le_succ _)
      · obtain ⟨i, -, -, d₀, -, hcase⟩ := tryPreds_some
          (fun j' d x hx => searchPath_mono usedL k j' d x hx) j _ dead P hP
        rcases hcase with ⟨-, rfl⟩ | ⟨j', P', -, hsr, rfl⟩
        · simp
        · have := searchPath_length_le usedL k j' d₀ P' hsr
          simp only [List.length_cons]
          omega

/-- Every path of `phaseAux` at level `k` has at most `k + 1` pairs. -/
theorem phaseAux_length_le (k : ℕ) : ∀ (js : List (Fin b)) (usedL : Fin a → Bool)
    (usedR : Fin b → Bool), ∀ P ∈ phaseAux adj mate k js usedL usedR, P.length ≤ k + 1
  | [], _, _ => by simp [phaseAux]
  | j :: js, usedL, usedR => by
      simp only [phaseAux]
      cases hs : searchPath adj mate usedL k j usedR with
      | mk r dead =>
          cases r with
          | none => exact phaseAux_length_le k js usedL dead
          | some P₀ =>
              intro P hP
              rcases List.mem_cons.1 hP with rfl | hP
              · exact searchPath_length_le usedL k j usedR P (by rw [hs])
              · exact phaseAux_length_le k js _ _ P hP

/-- **Phases use shortest augmenting paths.** If `firstFreeRound` is `d`, every path of the phase
has exactly `d + 1` pairs, the least length of any augmenting path
(`le_length_of_isAugmentingPath`). -/
theorem length_of_mem_phase (hv : Valid adj mate) {d : ℕ} (hd : firstFreeRound adj mate = some d)
    {P : List (Fin a × Fin b)} (hP : P ∈ phase adj mate) : P.length = d + 1 := by
  simp only [phase, hd] at hP
  refine le_antisymm (phaseAux_length_le d _ _ _ P hP) ?_
  obtain ⟨j, hj⟩ := (phaseAux_spec hv d _ (fun _ => false) (fun _ => false)
    (fun j hj => mem_candidates.1 hj)).1 P hP
  exact le_length_of_isAugmentingPath hd hj

end Shortest

/-! ## Phases find maximal sets of shortest augmenting paths -/

/-- `z` is first reached in round `m + 1` of the layered search. -/
def ExactLevel (mate : Fin b → Option (Fin a)) (m : ℕ) (z : Fin b) : Prop :=
  z ∈ (layers adj mate (m + 1)).2 ∧ z ∉ (layers adj mate m).2

/-- An alternating chain from `z` that ends at an unmatched left vertex: an augmenting path from
`z` without the layer and distinctness conditions of `AltPath`. -/
def IsChainFrom (mate : Fin b → Option (Fin a)) (z : Fin b) (Q : List (Fin a × Fin b)) : Prop :=
  Q.head?.map Prod.snd = some z ∧ (∀ q ∈ Q, q.2 ∈ adj q.1 ∧ mate q.2 ≠ some q.1) ∧
    List.IsChain (fun p q => mate q.2 = some p.1) Q ∧ ∀ q ∈ Q.getLast?, Free mate q.1

/-- No escape from `z` avoiding `U` and `D`: no alternating chain from `z` of shortest length
(`m + 1` pairs when `z` is first reached in round `m + 1`) whose left vertices are not in `U` and
whose right vertices after `z` are not in `D`. A phase gives this property to every right vertex
it marks dead after a failed search (`searchPath_dead`). -/
def NoEscape (mate : Fin b → Option (Fin a)) (U : Fin a → Bool) (D : Fin b → Bool) (z : Fin b) :
    Prop :=
  ∀ (m : ℕ) (Q : List (Fin a × Fin b)), ExactLevel adj mate m z → IsChainFrom adj mate z Q →
    Q.length = m + 1 → (∀ q ∈ Q, U q.1 = false) → (∀ q ∈ Q.tail, D q.2 = false) → False

section Maximal

variable {adj} {mate : Fin b → Option (Fin a)}

theorem ExactLevel.unique {m m' : ℕ} {z : Fin b} (h : ExactLevel adj mate m z)
    (h' : ExactLevel adj mate m' z) : m = m' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2 (layers_snd_mono (by omega) h.1)
  · exact h.2 (layers_snd_mono (by omega) h'.1)

theorem NoEscape.mono {U U' : Fin a → Bool} {D D' : Fin b → Bool} {z : Fin b}
    (h : NoEscape adj mate U D z) (hU : ∀ i, U i = true → U' i = true)
    (hD : ∀ x, D x = true → D' x = true) : NoEscape adj mate U' D' z := by
  intro m Q hm hQ hlen hU' hD'
  refine h m Q hm hQ hlen (fun q hq => ?_) (fun q hq => ?_)
  · cases hx : U q.1
    · rfl
    · have := hU' q hq; rw [hU _ hx] at this; exact absurd this (by simp)
  · cases hx : D q.2
    · rfl
    · have := hD' q hq; rw [hD _ hx] at this; exact absurd this (by simp)

theorem partnerOf_eq_none_of_free {i : Fin a} (h : Free mate i) : partnerOf mate i = none := by
  simp only [partnerOf, List.find?_eq_none, decide_eq_true_eq]
  exact fun j _ => h j

/-- The second right vertex of a shortest chain is first reached one round earlier. -/
theorem ExactLevel.tail {m : ℕ} {z : Fin b} {s s' : Fin a × Fin b} {S : List (Fin a × Fin b)}
    (hz : ExactLevel adj mate m z) (hQ : IsChainFrom adj mate z (s :: s' :: S))
    (hlen : (s :: s' :: S).length = m + 1) :
    ∃ m', m = m' + 1 ∧ ExactLevel adj mate m' s'.2 ∧ IsChainFrom adj mate s'.2 (s' :: S) := by
  obtain ⟨hh, he, hc, hl⟩ := hQ
  have hsz : s.2 = z := by simpa using hh
  have hm : m = S.length + 1 := by simp only [List.length_cons] at hlen; omega
  have hQ' : IsChainFrom adj mate s'.2 (s' :: S) :=
    ⟨rfl, fun q hq => he q (List.mem_cons_of_mem _ hq), (List.isChain_cons_cons.1 hc).2,
      by rwa [List.getLast?_cons_cons] at hl⟩
  refine ⟨S.length, hm, ⟨?_, ?_⟩, hQ'⟩
  · have := mem_layers_length (s' :: S) hQ'.2.1 hQ'.2.2.1 hQ'.2.2.2 s' (by simp)
    simpa using this
  · intro h
    have hmate : mate s'.2 = some s.1 := (List.isChain_cons_cons.1 hc).1
    cases hS : S.length with
    | zero => rw [hS, layers_zero_snd] at h; simp at h
    | succ n =>
        rw [hS] at h
        have hi : s.1 ∈ (layers adj mate (n + 1)).1 := mem_layers_succ_fst.2 (Or.inr ⟨_, h, hmate⟩)
        have : z ∈ (layers adj mate (n + 1 + 1)).2 := by
          rw [← hsz]; exact mem_layers_succ_snd.2 ⟨s.1, hi, he s List.mem_cons_self⟩
        exact hz.2 (by rw [hm, hS]; exact this)

/-- The partner of a candidate predecessor of a right vertex first reached in round `k + 2` is
first reached in round `k + 1`. -/
theorem ExactLevel.partner (hv : Valid adj mate) {k : ℕ} {z j' : Fin b} {i : Fin a}
    (hz : ExactLevel adj mate (k + 1) z) (hi : i ∈ (layers adj mate (k + 1)).1)
    (hadj : z ∈ adj i) (hm : mate z ≠ some i) (hp : mate j' = some i) :
    ExactLevel adj mate k j' := by
  refine ⟨?_, fun hj' => ?_⟩
  · obtain ⟨j'', hj''R, hj''m⟩ := exists_mate_of_mem_layers hi (fun hf => hf j' hp)
    rw [hv.inj i j' j'' hp hj''m]; exact hj''R
  · cases k with
    | zero => rw [layers_zero_snd] at hj'; simp at hj'
    | succ n =>
        have hi' : i ∈ (layers adj mate (n + 1)).1 := mem_layers_succ_fst.2 (Or.inr ⟨j', hj', hp⟩)
        exact hz.2 (mem_layers_succ_snd.2 ⟨i, hi', hadj, hm⟩)

/-- Every right vertex that `tryPreds` newly marks dead is either `j` itself, after every candidate
failed, or was marked by the search from the partner of a candidate. -/
theorem tryPreds_dead {ok : Fin a → Bool} {partner : Fin a → Option (Fin b)}
    {search : Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)}
    (hs : ∀ j' d x, d x = true → (search j' d).2 x = true) (j : Fin b) :
    ∀ (is : List (Fin a)) (D : Fin b → Bool) (y : Fin b),
      (tryPreds ok partner search j is D).2 y = true → D y = false →
      ((tryPreds ok partner search j is D).1 = none ∧ y = j) ∨
        ∃ i ∈ is, ok i = true ∧ ∃ j' d, partner i = some j' ∧ (∀ x, D x = true → d x = true) ∧
          (search j' d).2 y = true ∧ d y = false ∧
          ∀ x, (search j' d).2 x = true → (tryPreds ok partner search j is D).2 x = true
  | [], D, y, hy, hD => by
      left
      refine ⟨rfl, ?_⟩
      simp only [tryPreds, markDead, Bool.or_eq_true, decide_eq_true_eq] at hy
      rcases hy with h | h
      · rw [hD] at h; exact absurd h (by simp)
      · exact h
  | i :: is, D, y, hy, hD => by
      by_cases hok : ok i = true
      · cases hp : partner i with
        | none =>
            simp only [tryPreds, hok, ↓reduceIte, hp] at hy
            rw [hD] at hy; exact absurd hy (by simp)
        | some j' =>
            cases hsr : search j' D with
            | mk r d' =>
                cases r with
                | some P =>
                    simp only [tryPreds, hok, ↓reduceIte, hp, hsr] at hy ⊢
                    right
                    exact ⟨i, List.mem_cons_self, hok, j', D, hp, fun _ h => h,
                      by rw [hsr]; exact hy, hD, fun x hx => by rw [hsr] at hx; exact hx⟩
                | none =>
                    simp only [tryPreds, hok, ↓reduceIte, hp, hsr] at hy ⊢
                    by_cases hd' : d' y = true
                    · right
                      refine ⟨i, List.mem_cons_self, hok, j', D, hp, fun _ h => h,
                        by rw [hsr]; exact hd', hD, fun x hx => ?_⟩
                      rw [hsr] at hx
                      exact tryPreds_mono hs j is d' x hx
                    · have hd'f : d' y = false := by simpa using hd'
                      rcases tryPreds_dead hs j is d' y hy hd'f with h | ⟨i₁, hi₁, hok₁, j₁, d₁,
                        hp₁, hsub, h1, h2, h3⟩
                      · left; exact h
                      · right
                        refine ⟨i₁, List.mem_cons_of_mem _ hi₁, hok₁, j₁, d₁, hp₁,
                          fun x hx => hsub x ?_, h1, h2, h3⟩
                        have := hs j' D x hx
                        rwa [hsr] at this
      · have hok' : ok i = false := by simpa using hok
        simp only [tryPreds, hok', Bool.false_eq_true, ↓reduceIte] at hy ⊢
        rcases tryPreds_dead hs j is D y hy hD with h | ⟨i₁, hi₁, rest⟩
        · left; exact h
        · right; exact ⟨i₁, List.mem_cons_of_mem _ hi₁, rest⟩

/-- When `tryPreds` fails, `j` is marked dead and every candidate passing `ok` has a partner whose
search failed with a dead set contained in the final one. -/
theorem tryPreds_none {ok : Fin a → Bool} {partner : Fin a → Option (Fin b)}
    {search : Fin b → (Fin b → Bool) → Option (List (Fin a × Fin b)) × (Fin b → Bool)}
    (hs : ∀ j' d x, d x = true → (search j' d).2 x = true) (j : Fin b) :
    ∀ (is : List (Fin a)) (D : Fin b → Bool), (tryPreds ok partner search j is D).1 = none →
      (tryPreds ok partner search j is D).2 j = true ∧
      ∀ i ∈ is, ok i = true → ∃ j' d, partner i = some j' ∧ (search j' d).1 = none ∧
        ∀ x, (search j' d).2 x = true → (tryPreds ok partner search j is D).2 x = true
  | [], D, _ => ⟨by simp [tryPreds, markDead], by simp⟩
  | i :: is, D, h => by
      by_cases hok : ok i = true
      · cases hp : partner i with
        | none => simp [tryPreds, hok, hp] at h
        | some j' =>
            cases hsr : search j' D with
            | mk r d' =>
                cases r with
                | some P => simp [tryPreds, hok, hp, hsr] at h
                | none =>
                    simp only [tryPreds, hok, ↓reduceIte, hp, hsr] at h ⊢
                    obtain ⟨h1, h2⟩ := tryPreds_none hs j is d' h
                    refine ⟨h1, fun i₁ hi₁ hok₁ => ?_⟩
                    rcases List.mem_cons.1 hi₁ with rfl | hi₁
                    · exact ⟨j', D, hp, by rw [hsr],
                        fun x hx => by rw [hsr] at hx; exact tryPreds_mono hs j is d' x hx⟩
                    · exact h2 i₁ hi₁ hok₁
      · have hok' : ok i = false := by simpa using hok
        simp only [tryPreds, hok', Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨h1, h2⟩ := tryPreds_none hs j is D h
        refine ⟨h1, fun i₁ hi₁ hok₁ => ?_⟩
        rcases List.mem_cons.1 hi₁ with rfl | hi₁
        · rw [hok'] at hok₁; exact absurd hok₁ (by simp)
        · exact h2 i₁ hi₁ hok₁

/-- A failed search marks its start dead. -/
theorem searchPath_none_marks (U : Fin a → Bool) : ∀ (k : ℕ) (z : Fin b) (D : Fin b → Bool),
    (searchPath adj mate U k z D).1 = none → (searchPath adj mate U k z D).2 z = true
  | 0, z, D, h => by
      simp only [searchPath] at h ⊢
      split_ifs at h ⊢ with hz
      · exact hz
      · exact (tryPreds_none (fun _ d x hx => hx) z _ D h).1
  | k + 1, z, D, h => by
      simp only [searchPath] at h ⊢
      split_ifs at h ⊢ with hz hzk
      · exact hz
      · exact searchPath_none_marks U k z D h
      · exact (tryPreds_none (fun j' d x hx => searchPath_mono U k j' d x hx) z _ D h).1

/-- **Dead vertices have no escape.** Every right vertex that a search from a vertex first reached
in round `k + 1` newly marks dead has no shortest escape avoiding the used left vertices and the
final dead set: Hopcroft and Karp's pruning loses no path. -/
theorem searchPath_dead (hv : Valid adj mate) (U : Fin a → Bool) : ∀ (k : ℕ) (z : Fin b)
    (D : Fin b → Bool), ExactLevel adj mate k z → ∀ y,
      (searchPath adj mate U k z D).2 y = true → D y = false →
      NoEscape adj mate U (searchPath adj mate U k z D).2 y
  | 0, z, D, hz, y, hy, hD => by
      simp only [searchPath] at hy ⊢
      split_ifs at hy ⊢ with hzd
      · simp only at hy; rw [hD] at hy; exact absurd hy (by simp)
      · rcases tryPreds_dead (fun _ d x hx => hx) z _ D y hy hD with ⟨hnone, rfl⟩ |
          ⟨i, -, -, j', d, -, -, h1, h2, -⟩
        · intro m Q hm hQ hlen hU _
          have hm0 : m = 0 := hm.unique hz
          subst hm0
          obtain ⟨q, rfl⟩ : ∃ q, Q = [q] := by
            match Q, hlen with
            | [q], _ => exact ⟨q, rfl⟩
          obtain ⟨hh, he, -, hl⟩ := hQ
          have hqz : q.2 = y := by simpa using hh
          have hfree : Free mate q.1 := hl q (by simp)
          have hok : decide (q.1 ∈ (layers adj mate 0).1 ∧ y ∈ adj q.1 ∧ mate y ≠ some q.1 ∧
              U q.1 = false) = true := by
            rw [← hqz]
            simpa [mem_layers_zero_fst.2 hfree] using
              ⟨(he q (by simp)).1, (he q (by simp)).2, hU q (by simp)⟩
          obtain ⟨j', -, hp, -⟩ := (tryPreds_none (fun _ d x hx => hx) y _ D hnone).2 q.1
            (List.mem_finRange _) hok
          exact hfree j' (partnerOf_eq_some hp)
        · simp only at h1; rw [h2] at h1; exact absurd h1 (by simp)
  | k + 1, z, D, hz, y, hy, hD => by
      simp only [searchPath] at hy ⊢
      split_ifs at hy ⊢ with hzd hzk
      · simp only at hy; rw [hD] at hy; exact absurd hy (by simp)
      · exact absurd hzk hz.2
      · have hs : ∀ j' (d : Fin b → Bool) x, d x = true →
            (searchPath adj mate U k j' d).2 x = true :=
          fun j' d x hx => searchPath_mono U k j' d x hx
        rcases tryPreds_dead hs z _ D y hy hD with ⟨hnone, rfl⟩ |
          ⟨i, -, hok, j', d, hp, -, h1, h2, h3⟩
        · intro m Q hm hQ hlen hU hD'
          have hmk : m = k + 1 := hm.unique hz
          subst hmk
          obtain ⟨q, q', S, rfl⟩ : ∃ q q' S, Q = q :: q' :: S := by
            match Q, hlen with
            | q :: q' :: S, _ => exact ⟨q, q', S, rfl⟩
          obtain ⟨hh, he, hc, hl⟩ := hQ
          have hqz : q.2 = y := by simpa using hh
          have hmate : mate q'.2 = some q.1 := (List.isChain_cons_cons.1 hc).1
          have hq'R : q'.2 ∈ (layers adj mate (k + 1)).2 := by
            have := mem_layers_length (q' :: S) (fun p hp => he p (List.mem_cons_of_mem _ hp))
              (List.isChain_cons_cons.1 hc).2 (by rwa [List.getLast?_cons_cons] at hl) q'
              (by simp)
            simp only [List.length_cons, List.length_cons] at hlen this
            rwa [show S.length + 1 = k + 1 by omega] at this
          have hqL : q.1 ∈ (layers adj mate (k + 1)).1 :=
            mem_layers_succ_fst.2 (Or.inr ⟨q'.2, hq'R, hmate⟩)
          have hok : decide (q.1 ∈ (layers adj mate (k + 1)).1 ∧ y ∈ adj q.1 ∧
              mate y ≠ some q.1 ∧ U q.1 = false) = true := by
            rw [← hqz]
            simpa [hqL] using ⟨(he q (by simp)).1, (he q (by simp)).2, hU q (by simp)⟩
          obtain ⟨j', d, hp, hnone', hsub⟩ := (tryPreds_none hs y _ D hnone).2 q.1
            (List.mem_finRange _) hok
          have hj' : j' = q'.2 := hv.inj q.1 j' q'.2 (partnerOf_eq_some hp) hmate
          have := hsub j' (searchPath_none_marks U k j' d hnone')
          rw [hj', hD' q' (by simp)] at this
          exact absurd this (by simp)
        · simp only [decide_eq_true_eq] at hok
          obtain ⟨hiL, hiadj, him, -⟩ := hok
          have hj' : ExactLevel adj mate k j' :=
            hz.partner hv hiL hiadj him (partnerOf_eq_some hp)
          exact (searchPath_dead hv U k j' d hj' y h1 h2).mono (fun _ h => h) h3

/-- Along a shortest chain that avoids the vertices of earlier paths, a dead set whose members are
on earlier paths or have no escape contains no right vertex of the chain. -/
theorem not_dead_of_chain {U : Fin a → Bool} {D : Fin b → Bool} {Lf : Fin a → Prop}
    {Rf : Fin b → Prop} (hU : ∀ i, U i = true → Lf i)
    (hD : ∀ y, D y = true → NoEscape adj mate U D y ∨ Rf y) :
    ∀ (S : List (Fin a × Fin b)) (z : Fin b) (m : ℕ), IsChainFrom adj mate z S →
      ExactLevel adj mate m z → S.length = m + 1 → (∀ q ∈ S, ¬ Lf q.1 ∧ ¬ Rf q.2) →
      ∀ q ∈ S, D q.2 = false
  | [], _, _, _, _, _, _ => by simp
  | s :: S, z, m, hS, hz, hlen, havoid => by
      have htail : ∀ q ∈ S, D q.2 = false := by
        cases S with
        | nil => simp
        | cons s' S' =>
            obtain ⟨m', rfl, hz', hS'⟩ := hz.tail hS hlen
            exact not_dead_of_chain hU hD (s' :: S') s'.2 m' hS' hz'
              (by simp only [List.length_cons] at hlen ⊢; omega)
              (fun q hq => havoid q (List.mem_cons_of_mem _ hq))
      have hsz : s.2 = z := by simpa using hS.1
      have hUf : ∀ q ∈ s :: S, U q.1 = false := fun q hq => by
        cases hx : U q.1
        · rfl
        · exact absurd (hU _ hx) (havoid q hq).1
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · cases hDq : D q.2
        · rfl
        · exfalso
          rcases hD q.2 hDq with hne | hR
          · rw [hsz] at hne
            exact hne m (q :: S) hz hS hlen hUf htail
          · exact (havoid q List.mem_cons_self).2 hR
      · exact htail q hq

/-- The invariant of a phase: a shortest chain from `j` (first reached in round `d + 1`) that avoids
the earlier paths `F` and the paths found from the candidates `js` cannot exist while `j` is still
a candidate or dead. -/
theorem phaseAux_maximal (hv : Valid adj mate) (d : ℕ) {j : Fin b} {Q : List (Fin a × Fin b)}
    (hQ : IsChainFrom adj mate j Q) (hj : ExactLevel adj mate d j) (hlen : Q.length = d + 1) :
    ∀ (js : List (Fin b)) (U : Fin a → Bool) (D : Fin b → Bool) (F : List (List (Fin a × Fin b))),
      (∀ j' ∈ js, ExactLevel adj mate d j') →
      (∀ i, U i = true → ∃ P ∈ F, i ∈ P.map Prod.fst) →
      (∀ y, D y = true → NoEscape adj mate U D y ∨ ∃ P ∈ F, y ∈ P.map Prod.snd) →
      (j ∈ js ∨ D j = true) →
      (∀ P ∈ F ++ phaseAux adj mate d js U D, ∀ q ∈ Q,
        q.1 ∉ P.map Prod.fst ∧ q.2 ∉ P.map Prod.snd) → False
  | [], U, D, F, _, hU, hD, hjd, hdis => by
      have hDj : D j = true := by simpa using hjd
      have hav : ∀ q ∈ Q, ¬ (∃ P ∈ F, q.1 ∈ P.map Prod.fst) ∧
          ¬ (∃ P ∈ F, q.2 ∈ P.map Prod.snd) := fun q hq =>
        ⟨fun ⟨P, hP, h⟩ => (hdis P (List.mem_append_left _ hP) q hq).1 h,
          fun ⟨P, hP, h⟩ => (hdis P (List.mem_append_left _ hP) q hq).2 h⟩
      have hnd := not_dead_of_chain hU hD Q j d hQ hj hlen hav
      cases Q with
      | nil => simp at hlen
      | cons q Q =>
          have hqj : q.2 = j := by simpa using hQ.1
          have := hnd q List.mem_cons_self
          rw [hqj, hDj] at this
          exact absurd this (by simp)
  | j₀ :: js, U, D, F, hjs, hU, hD, hjd, hdis => by
      have hjs' : ∀ j' ∈ js, ExactLevel adj mate d j' :=
        fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')
      have hj₀ := hjs j₀ List.mem_cons_self
      have hmono : ∀ x, D x = true → (searchPath adj mate U d j₀ D).2 x = true :=
        fun x hx => searchPath_mono U d j₀ D x hx
      -- dead vertices after the search: earlier ones, or newly marked ones without escape
      have hD₁ : ∀ y, (searchPath adj mate U d j₀ D).2 y = true →
          NoEscape adj mate U (searchPath adj mate U d j₀ D).2 y ∨
            ∃ P ∈ F, y ∈ P.map Prod.snd := by
        intro y hy
        cases hDy : D y
        · exact Or.inl (searchPath_dead hv U d j₀ D hj₀ y hy hDy)
        · rcases hD y hDy with h | h
          · exact Or.inl (h.mono (fun _ h => h) hmono)
          · exact Or.inr h
      cases hs : searchPath adj mate U d j₀ D with
      | mk r D₁ =>
          rw [hs] at hmono hD₁
          simp only at hmono hD₁
          cases r with
          | none =>
              have hmark : D₁ j₀ = true := by
                have := searchPath_none_marks U d j₀ D (by rw [hs])
                rwa [hs] at this
              refine phaseAux_maximal hv d hQ hj hlen js U D₁ F hjs' hU hD₁ ?_ ?_
              · rcases hjd with h | h
                · rcases List.mem_cons.1 h with rfl | h
                  · exact Or.inr hmark
                  · exact Or.inl h
                · exact Or.inr (hmono j h)
              · intro P hP q hq
                apply hdis P _ q hq
                simpa [phaseAux, hs] using hP
          | some P₀ =>
              have hP₀ := (searchPath_spec hv U d j₀ D P₀ hj₀.1 (by rw [hs])).1
              have hj₀P : j₀ ∈ P₀.map Prod.snd := by
                cases P₀ with
                | nil => simpa using hP₀.head
                | cons p P =>
                    simp only [List.map_cons, List.mem_cons]
                    left
                    simpa using hP₀.head.symm
              refine phaseAux_maximal hv d hQ hj hlen js (markL U P₀) (markR D₁ P₀) (F ++ [P₀])
                hjs' ?_ ?_ ?_ ?_
              · intro i hi
                simp only [markL, Bool.or_eq_true, decide_eq_true_eq] at hi
                rcases hi with hi | hi
                · obtain ⟨P, hP, h⟩ := hU i hi
                  exact ⟨P, List.mem_append_left _ hP, h⟩
                · exact ⟨P₀, by simp, hi⟩
              · intro y hy
                simp only [markR, Bool.or_eq_true, decide_eq_true_eq] at hy
                rcases hy with hy | hy
                · rcases hD₁ y hy with h | ⟨P, hP, h⟩
                  · refine Or.inl (h.mono (fun i hi => ?_) (fun x hx => ?_))
                    · simp [markL, hi]
                    · simp [markR, hx]
                  · exact Or.inr ⟨P, List.mem_append_left _ hP, h⟩
                · exact Or.inr ⟨P₀, by simp, hy⟩
              · rcases hjd with h | h
                · rcases List.mem_cons.1 h with rfl | h
                  · right; simp [markR, hj₀P]
                  · exact Or.inl h
                · right; simp [markR, hmono j h]
              · intro P hP q hq
                apply hdis P _ q hq
                simp only [phaseAux, hs, List.mem_append, List.mem_cons] at hP ⊢
                tauto

/-- **Phases are maximal.** If `firstFreeRound` is `d`, every shortest augmenting path (`d + 1`
pairs, the least length by `le_length_of_isAugmentingPath`) shares a vertex with a path of the
phase: the phase's vertex-disjoint shortest augmenting paths form a maximal set, as Hopcroft and
Karp require. -/
theorem phase_maximal (hv : Valid adj mate) {d k : ℕ} (hd : firstFreeRound adj mate = some d)
    {j : Fin b} {Q : List (Fin a × Fin b)} (hQ : IsAugmentingPath adj mate k j Q)
    (hlen : Q.length = d + 1) :
    ∃ P ∈ phase adj mate, ∃ q ∈ Q, q.1 ∈ P.map Prod.fst ∨ q.2 ∈ P.map Prod.snd := by
  obtain ⟨-, -, hmin⟩ := firstFreeRound_eq_some.1 hd
  have hexact : ∀ j', mate j' = none → j' ∈ (layers adj mate (d + 1)).2 →
      ExactLevel adj mate d j' := by
    intro j' hfree hR
    refine ⟨hR, fun h => ?_⟩
    cases d with
    | zero => rw [layers_zero_snd] at h; simp at h
    | succ n => exact hmin n (Nat.lt_succ_self n) j' hfree h
  have hchain : IsChainFrom adj mate j Q := ⟨hQ.head, hQ.edge, hQ.chain, hQ.last⟩
  have hjR : j ∈ (layers adj mate (d + 1)).2 := by
    cases Q with
    | nil => simp at hlen
    | cons q Q =>
        have hqj : q.2 = j := by simpa using hQ.head
        have := mem_layers_length (q :: Q) hQ.edge hQ.chain hQ.last q (by simp)
        rwa [hlen, hqj] at this
  by_contra hno
  push Not at hno
  simp only [phase, hd] at hno
  exact phaseAux_maximal hv d hchain (hexact j hQ.start_free hjR) hlen _ (fun _ => false)
    (fun _ => false) [] (fun j' hj' => hexact j' (mem_candidates.1 hj').1 (mem_candidates.1 hj').2)
    (by simp) (by simp) (Or.inl (mem_candidates.2 ⟨hQ.start_free, hjR⟩))
    (fun P hP q hq => by simpa using hno P (by simpa using hP) q hq)

end Maximal

/-! ## Distances do not decrease across a phase -/

section Monotone

variable {adj} {mate : Fin b → Option (Fin a)}

/-- A matched right vertex is reached in the same round as its partner. -/
theorem mem_layers_snd_of_mate (hv : Valid adj mate) {k : ℕ} {i : Fin a} {j : Fin b}
    (hm : mate j = some i) (hi : i ∈ (layers adj mate k).1) : j ∈ (layers adj mate k).2 := by
  obtain ⟨j'', hj'', hm''⟩ := exists_mate_of_mem_layers hi (fun hf => hf j hm)
  rw [hv.inj i j j'' hm hm'']; exact hj''

/-- Along a shortest chain, each pair `(i, j)` has `j` first reached in some round `m + 1` and `i`
reached by round `m`. -/
theorem pair_levels_of_chain : ∀ (S : List (Fin a × Fin b)) (z : Fin b) (m : ℕ),
    IsChainFrom adj mate z S → ExactLevel adj mate m z → S.length = m + 1 →
    ∀ p ∈ S, ∃ m', ExactLevel adj mate m' p.2 ∧ p.1 ∈ (layers adj mate m').1
  | [], _, _, _, _, _ => by simp
  | s :: S, z, m, hS, hz, hlen => by
      have hsz : s.2 = z := by simpa using hS.1
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨m, hsz ▸ hz, ?_⟩
        cases S with
        | nil =>
            have : Free mate p.1 := hS.2.2.2 p (by simp)
            exact layers_fst_mono (Nat.zero_le m) (mem_layers_zero_fst.2 this)
        | cons s' S' =>
            obtain ⟨m', rfl, hz', -⟩ := hz.tail hS hlen
            have hmate : mate s'.2 = some p.1 := (List.isChain_cons_cons.1 hS.2.2.1).1
            exact mem_layers_succ_fst.2 (Or.inr ⟨s'.2, hz'.1, hmate⟩)
      · cases S with
        | nil => simp at hp
        | cons s' S' =>
            obtain ⟨m', rfl, hz', hS'⟩ := hz.tail hS hlen
            exact pair_levels_of_chain (s' :: S') s'.2 m' hS' hz'
              (by simp only [List.length_cons] at hlen ⊢; omega) p hp

/-- Every pair of a phase has its right vertex first reached in some round `m + 1` and its left
vertex reached by round `m`. -/
theorem pair_levels_of_mem_phase (hv : Valid adj mate) {d : ℕ}
    (hd : firstFreeRound adj mate = some d) {p : Fin a × Fin b}
    (hp : p ∈ (phase adj mate).flatten) :
    ∃ m, ExactLevel adj mate m p.2 ∧ p.1 ∈ (layers adj mate m).1 := by
  obtain ⟨P, hP, hpP⟩ := List.mem_flatten.1 hp
  have hlen := length_of_mem_phase hv hd hP
  have hP' := hP
  simp only [phase, hd] at hP'
  obtain ⟨j, hj⟩ := (phaseAux_spec hv d _ (fun _ => false) (fun _ => false)
    (fun j hj => mem_candidates.1 hj)).1 P hP'
  obtain ⟨-, -, hmin⟩ := firstFreeRound_eq_some.1 hd
  have hjR : j ∈ (layers adj mate (d + 1)).2 := by
    cases P with
    | nil => simp at hlen
    | cons q Q =>
        have hqj : q.2 = j := by simpa using hj.head
        have := mem_layers_length (q :: Q) hj.edge hj.chain hj.last q (by simp)
        rwa [hlen, hqj] at this
  have hjx : ExactLevel adj mate d j := by
    refine ⟨hjR, fun h => ?_⟩
    cases d with
    | zero => rw [layers_zero_snd] at h; simp at h
    | succ n => exact hmin n (Nat.lt_succ_self n) j hj.start_free h
  exact pair_levels_of_chain P j d ⟨hj.head, hj.edge, hj.chain, hj.last⟩ hjx hlen p hpP

/-- A left vertex unmatched after a phase was unmatched before it: the first pair of each path
starts at an unmatched right vertex, and every other right vertex of a path had the previous left
vertex as partner, which the phase rematches. -/
theorem free_of_free_flip (hv : Valid adj mate) {d : ℕ} (hd : firstFreeRound adj mate = some d)
    {i : Fin a} (h : Free (flip mate (phase adj mate).flatten) i) : Free mate i := by
  have hspec := phaseAux_spec hv d (((List.finRange b).filter fun j => decide (mate j = none ∧
    j ∈ (layers adj mate (d + 1)).2))) (fun _ => false) (fun _ => false)
    (fun j hj => mem_candidates.1 hj)
  have hph : phase adj mate = phaseAux adj mate d ((List.finRange b).filter fun j =>
      decide (mate j = none ∧ j ∈ (layers adj mate (d + 1)).2)) (fun _ => false) (fun _ => false) :=
    by simp only [phase, hd]
  rw [← hph] at hspec
  obtain ⟨hpaths, -, hn, -⟩ := hspec
  intro j hmj
  by_cases hjP : ∃ p ∈ (phase adj mate).flatten, p.2 = j
  · obtain ⟨p, hp, rfl⟩ := hjP
    obtain ⟨P, hP, hpP⟩ := List.mem_flatten.1 hp
    obtain ⟨j₀, hj₀⟩ := hpaths P hP
    rcases head_or_pred hj₀.chain p hpP with hh | ⟨q, hq, hqp⟩
    · have : p.2 = j₀ := by simpa [hh] using hj₀.head
      rw [this, hj₀.start_free] at hmj
      exact absurd hmj (by simp)
    · rw [hmj] at hqp
      have hqi : q.1 = i := (Option.some.inj hqp).symm
      have hq' : q ∈ (phase adj mate).flatten := List.mem_flatten.2 ⟨P, hP, hq⟩
      have := (flip_eq_some (mate := mate) (i := q.1) (j := q.2) hn).2 (Or.inl (by simpa using hq'))
      rw [hqi] at this
      exact h q.2 this
  · push Not at hjP
    exact h j ((flip_eq_some (mate := mate) hn).2 (Or.inr ⟨hjP, hmj⟩))

/-- **Distances do not decrease across a phase** (Hopcroft and Karp): after flipping the paths of a
phase, every vertex reached by round `k` of the layered search was already reached by round `k`
before. -/
theorem layers_flip_phase_subset (hv : Valid adj mate) {d : ℕ}
    (hd : firstFreeRound adj mate = some d) : ∀ k : ℕ,
    (layers adj (flip mate (phase adj mate).flatten) k).1 ⊆ (layers adj mate k).1 ∧
      (layers adj (flip mate (phase adj mate).flatten) k).2 ⊆ (layers adj mate k).2
  | 0 => ⟨fun i hi => mem_layers_zero_fst.2 (free_of_free_flip hv hd (mem_layers_zero_fst.1 hi)),
      by simp [layers_zero_snd]⟩
  | k + 1 => by
      obtain ⟨ih₁, -⟩ := layers_flip_phase_subset hv hd k
      have hn : ((phase adj mate).flatten.map Prod.snd).Nodup := by
        have hspec := phaseAux_spec hv d (((List.finRange b).filter fun j => decide (mate j = none ∧
          j ∈ (layers adj mate (d + 1)).2))) (fun _ => false) (fun _ => false)
          (fun j hj => mem_candidates.1 hj)
        simpa only [phase, hd] using hspec.2.2.1
      have hR : (layers adj (flip mate (phase adj mate).flatten) (k + 1)).2 ⊆
          (layers adj mate (k + 1)).2 := by
        intro j hj
        obtain ⟨i, hi, hadj, -⟩ := mem_layers_succ_snd.1 hj
        have hi₀ := ih₁ hi
        by_cases hm : mate j = some i
        · exact layers_snd_mono (Nat.le_succ k) (mem_layers_snd_of_mate hv hm hi₀)
        · exact mem_layers_succ_snd.2 ⟨i, hi₀, hadj, hm⟩
      refine ⟨fun i hi => ?_, hR⟩
      rcases mem_layers_succ_fst.1 hi with hi | ⟨j, hj, hm'⟩
      · exact layers_fst_mono (Nat.le_succ k) (ih₁ hi)
      · have hj₀ := hR hj
        rcases (flip_eq_some (mate := mate) hn).1 hm' with hij | ⟨-, hm⟩
        · obtain ⟨m, hm, hpm⟩ := pair_levels_of_mem_phase hv hd hij
          have hmk : m ≤ k := by
            by_contra hlt
            exact hm.2 (layers_snd_mono (by omega) hj₀)
          exact layers_fst_mono (by omega) hpm
        · exact mem_layers_succ_fst.2 (Or.inr ⟨j, hj₀, hm⟩)

/-- The next phase's paths are at least as long: if `firstFreeRound` is `d` before a phase and
`d'` after it, then `d ≤ d'`. -/
theorem le_firstFreeRound_flip_phase (hv : Valid adj mate) {d d' : ℕ}
    (hd : firstFreeRound adj mate = some d)
    (hd' : firstFreeRound adj (flip mate (phase adj mate).flatten) = some d') : d ≤ d' := by
  obtain ⟨-, ⟨j, hj, hjR⟩, -⟩ := firstFreeRound_eq_some.1 hd'
  obtain ⟨-, -, hmin⟩ := firstFreeRound_eq_some.1 hd
  have hfree : mate j = none := by
    cases hm : mate j with
    | none => rfl
    | some i =>
        exfalso
        unfold flip at hj
        cases hf : (phase adj mate).flatten.find? (fun p => decide (p.2 = j)) with
        | none => rw [hf] at hj; simp only at hj; rw [hm] at hj; exact absurd hj (by simp)
        | some p => rw [hf] at hj; exact absurd hj (by simp)
  by_contra hlt
  exact hmin d' (by omega) j hfree ((layers_flip_phase_subset hv hd (d' + 1)).2 hjR)

/-- The paths of a phase are augmenting paths at level `d`, with no left or right vertex twice. -/
theorem phase_spec (hv : Valid adj mate) {d : ℕ} (hd : firstFreeRound adj mate = some d) :
    (∀ P ∈ phase adj mate, ∃ j, IsAugmentingPath adj mate d j P) ∧
      ((phase adj mate).flatten.map Prod.fst).Nodup ∧
      ((phase adj mate).flatten.map Prod.snd).Nodup := by
  have hspec := phaseAux_spec hv d _ (fun _ => false) (fun _ => false)
    (fun j hj => mem_candidates.1 hj)
  simp only [phase, hd]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- A shortest chain after a phase, from a right vertex first reached in the same round before and
after it, is a chain before the phase too, and its right vertices after the first are not on the
phase's paths: a flipped edge would step back a round, which a shortest chain cannot afford. -/
theorem chain_of_chain_flip_phase (hv : Valid adj mate) {d : ℕ}
    (hd : firstFreeRound adj mate = some d) :
    ∀ (S : List (Fin a × Fin b)) (z : Fin b) (m : ℕ),
      IsChainFrom adj (flip mate (phase adj mate).flatten) z S → S.length = m + 1 →
      ExactLevel adj mate m z → ExactLevel adj (flip mate (phase adj mate).flatten) m z →
      IsChainFrom adj mate z S ∧ ∀ q ∈ S.tail, ∀ p ∈ (phase adj mate).flatten, p.2 ≠ q.2
  | [], _, _, _, hlen, _, _ => by simp at hlen
  | s :: S, z, m, hS, hlen, hz, hz' => by
      obtain ⟨-, -, hn⟩ := phase_spec hv hd
      have hsz : s.2 = z := by simpa using hS.1
      have hsub := layers_flip_phase_subset hv hd
      -- `s.1` is reached by round `m`, before and after the phase
      obtain ⟨m₀, hm₀, hs₁'⟩ := pair_levels_of_chain (mate := flip mate (phase adj mate).flatten)
        (s :: S) z m hS hz' hlen s List.mem_cons_self
      have hm₀m : m₀ = m := hm₀.unique (hsz ▸ hz')
      subst hm₀m
      have hs₁ : s.1 ∈ (layers adj mate m₀).1 := (hsub m₀).1 hs₁'
      have hedge : s.2 ∈ adj s.1 ∧ mate s.2 ≠ some s.1 := by
        refine ⟨(hS.2.1 s List.mem_cons_self).1, fun hm => ?_⟩
        exact hz.2 (hsz ▸ mem_layers_snd_of_mate hv hm hs₁)
      -- `s.1` is not reached before round `m₀`
      have hnot : ∀ k, k + 1 = m₀ → s.1 ∉ (layers adj mate k).1 := by
        intro k hk h
        exact hz.2 (hsz ▸ hk ▸ mem_layers_succ_snd.2 ⟨s.1, h, hedge⟩)
      cases S with
      | nil =>
          have hfree : Free mate s.1 :=
            free_of_free_flip hv hd (hS.2.2.2 s (by simp))
          refine ⟨⟨hS.1, ?_, List.isChain_singleton _, ?_⟩, by simp⟩
          · intro q hq; rw [List.mem_singleton] at hq; subst hq; exact hedge
          · intro q hq; simp only [List.getLast?_singleton, Option.mem_def,
              Option.some.injEq] at hq; subst hq; exact hfree
      | cons s' S' =>
          obtain ⟨m', rfl, hz'', hS'⟩ := hz'.tail hS hlen
          have hmate' : flip mate (phase adj mate).flatten s'.2 = some s.1 :=
            (List.isChain_cons_cons.1 hS.2.2.1).1
          have hs'R : s'.2 ∈ (layers adj mate (m' + 1)).2 := (hsub (m' + 1)).2 hz''.1
          -- the link `s'.2 → s.1` is an old matching edge, not a flipped one
          have hlink : mate s'.2 = some s.1 ∧ ∀ p ∈ (phase adj mate).flatten, p.2 ≠ s'.2 := by
            rcases (flip_eq_some (mate := mate) hn).1 hmate' with hp | ⟨hall, hm⟩
            · exfalso
              obtain ⟨m'', hm'', hpl⟩ := pair_levels_of_mem_phase hv hd hp
              have hle : m'' ≤ m' := by
                by_contra hlt
                exact hm''.2 (layers_snd_mono (by omega) hs'R)
              exact hnot m' rfl (layers_fst_mono hle hpl)
            · exact ⟨hm, hall⟩
          have hold : ExactLevel adj mate m' s'.2 := by
            refine ⟨hs'R, fun h => ?_⟩
            cases m' with
            | zero => rw [layers_zero_snd] at h; simp at h
            | succ n =>
                exact hnot (n + 1) rfl (mem_layers_succ_fst.2 (Or.inr ⟨s'.2, h, hlink.1⟩))
          obtain ⟨hchain, htail⟩ := chain_of_chain_flip_phase hv hd (s' :: S') s'.2 m' hS'
            (by simp only [List.length_cons] at hlen ⊢; omega) hold hz''
          refine ⟨⟨hS.1, ?_, ?_, ?_⟩, ?_⟩
          · intro q hq
            rcases List.mem_cons.1 hq with rfl | hq
            · exact hedge
            · exact hchain.2.1 q hq
          · exact List.isChain_cons_cons.2 ⟨hlink.1, hchain.2.2.1⟩
          · rw [List.getLast?_cons_cons]; exact hchain.2.2.2
          · intro q hq p hp
            rcases List.mem_cons.1 hq with rfl | hq
            · exact hlink.2 p hp
            · exact htail q hq p hp

/-- **The next phase's paths are strictly longer** (Hopcroft and Karp): if `firstFreeRound` is `d`
before a phase and `d'` after it, then `d < d'`. A shortest augmenting path after the phase of the
same length would be a shortest augmenting chain before it, disjoint from the phase's paths,
contradicting `phase_maximal`'s invariant. -/
theorem lt_firstFreeRound_flip_phase (hv : Valid adj mate) {d d' : ℕ}
    (hd : firstFreeRound adj mate = some d)
    (hd' : firstFreeRound adj (flip mate (phase adj mate).flatten) = some d') : d < d' := by
  rcases Nat.lt_or_eq_of_le (le_firstFreeRound_flip_phase hv hd hd') with h | h
  · exact h
  subst h
  exfalso
  obtain ⟨hpaths, hn₁, hn₂⟩ := phase_spec hv hd
  set mate' := flip mate (phase adj mate).flatten with hmate'
  have hv' : Valid adj mate' :=
    valid_flip_flatten hv (fun P hP => (hpaths P hP).imp fun _ h => h.toAltPath) hn₁ hn₂
  obtain ⟨-, ⟨j, hj, hjR'⟩, hmin'⟩ := firstFreeRound_eq_some.1 hd'
  obtain ⟨-, -, hmin⟩ := firstFreeRound_eq_some.1 hd
  -- `j` is unmatched before the phase as well
  have hjfree : mate j = none := by
    cases hm : mate j with
    | none => rfl
    | some i =>
        exfalso
        rcases (show (∃ p ∈ (phase adj mate).flatten, p.2 = j) ∨
            ∀ p ∈ (phase adj mate).flatten, p.2 ≠ j by
              by_cases h : ∃ p ∈ (phase adj mate).flatten, p.2 = j
              · exact Or.inl h
              · push Not at h; exact Or.inr h) with ⟨p, hp, rfl⟩ | hall
        · have := (flip_eq_some (mate := mate) (i := p.1) (j := p.2) hn₂).2
            (Or.inl (by simpa using hp))
          rw [← hmate', hj] at this; exact absurd this (by simp)
        · have := (flip_eq_some (mate := mate) (i := i) (j := j) hn₂).2 (Or.inr ⟨hall, hm⟩)
          rw [← hmate', hj] at this; exact absurd this (by simp)
  have hjx : ExactLevel adj mate d j := by
    refine ⟨(layers_flip_phase_subset hv hd (d + 1)).2 hjR', fun h => ?_⟩
    cases d with
    | zero => rw [layers_zero_snd] at h; simp at h
    | succ n => exact hmin n (Nat.lt_succ_self n) j hjfree h
  have hjx' : ExactLevel adj mate' d j := by
    refine ⟨hjR', fun h => ?_⟩
    cases d with
    | zero => rw [layers_zero_snd] at h; simp at h
    | succ n => exact hmin' n (Nat.lt_succ_self n) j hj h
  -- a shortest augmenting path after the phase
  obtain ⟨P', hP'⟩ := Option.isSome_iff_exists.1 (searchPath_isSome hv' d j hjR')
  have hP'alt := (searchPath_spec hv' (fun _ => false) d j (fun _ => false) P' hjR' hP').1
  have hP'aug : IsAugmentingPath adj mate' d j P' := ⟨hP'alt, hj⟩
  have hlen : P'.length = d + 1 :=
    le_antisymm (searchPath_length_le _ d j _ P' hP') (le_length_of_isAugmentingPath hd' hP'aug)
  have hchain' : IsChainFrom adj mate' j P' := ⟨hP'alt.head, hP'alt.edge, hP'alt.chain, hP'alt.last⟩
  obtain ⟨hchain, htail⟩ := chain_of_chain_flip_phase hv hd P' j d hchain' hlen hjx hjx'
  -- it avoids every path of the phase
  have hdis : ∀ P ∈ phase adj mate, ∀ q ∈ P',
      q.1 ∉ P.map Prod.fst ∧ q.2 ∉ P.map Prod.snd := by
    have hright : ∀ q ∈ P', ∀ p ∈ (phase adj mate).flatten, p.2 ≠ q.2 := by
      intro q hq p hp hpq
      cases P' with
      | nil => simp at hq
      | cons q₀ P'' =>
          rcases List.mem_cons.1 hq with rfl | hq
          · have hq₀ : q.2 = j := by simpa using hP'alt.head
            have := (flip_eq_some (mate := mate) (i := p.1) (j := p.2) hn₂).2
              (Or.inl (by simpa using hp))
            rw [hpq, hq₀, ← hmate', hj] at this
            exact absurd this (by simp)
          · exact htail q (by simpa using hq) p hp hpq
    intro P hP q hq
    refine ⟨fun hl => ?_, fun hr => ?_⟩
    · obtain ⟨p, hpP, hpq⟩ := List.mem_map.1 hl
      have hp : p ∈ (phase adj mate).flatten := List.mem_flatten.2 ⟨P, hP, hpP⟩
      have hmp : mate' p.2 = some q.1 := by
        rw [← hpq]
        exact (flip_eq_some (mate := mate) (i := p.1) (j := p.2) hn₂).2
          (Or.inl (by simpa using hp))
      rcases last_or_succ hP'alt.chain q hq with hlast | ⟨q', hq', hqq'⟩
      · exact hP'alt.last q (by rw [Option.mem_def]; exact hlast) p.2 hmp
      · have := hv'.inj q.1 q'.2 p.2 hqq' hmp
        exact hright q' hq' p hp this.symm
    · obtain ⟨p, hpP, hpq⟩ := List.mem_map.1 hr
      exact hright q hq p (List.mem_flatten.2 ⟨P, hP, hpP⟩) hpq
  have hexact : ∀ j', mate j' = none → j' ∈ (layers adj mate (d + 1)).2 →
      ExactLevel adj mate d j' := by
    intro j' hfree hR
    refine ⟨hR, fun h => ?_⟩
    cases d with
    | zero => rw [layers_zero_snd] at h; simp at h
    | succ n => exact hmin n (Nat.lt_succ_self n) j' hfree h
  have hph := hdis
  simp only [phase, hd] at hph
  exact phaseAux_maximal hv d hchain hjx hlen _ (fun _ => false) (fun _ => false) []
    (fun j' hj' => hexact j' (mem_candidates.1 hj').1 (mem_candidates.1 hj').2)
    (by simp) (by simp) (Or.inl (mem_candidates.2 ⟨hjfree, hjx.1⟩))
    (fun P hP q hq => hph P (by simpa using hP) q hq)

end Monotone

/-! ## `O(√V)` phases -/

section Sqrt

variable {adj} {mate : Fin b → Option (Fin a)}

/-- **One round of the layered search bounds the deficit.** If no unmatched right vertex is reached
by round `k + 1`, every matching has at most as many edges as the current one plus the right
vertices first reached in round `k + 1`: the unreached left vertices and the right vertices reached
by round `k + 1` cover every edge. -/
theorem card_le_card_pairs_add (hv : Valid adj mate) {M : Finset (Fin a × Fin b)}
    (hM : IsMatching adj M) {k : ℕ}
    (hk : ∀ j, mate j = none → j ∉ (layers adj mate (k + 1)).2) :
    M.card ≤ (pairs mate).card +
      ((layers adj mate (k + 1)).2 \ (layers adj mate k).2).card := by
  classical
  set Z := (layers adj mate k).1 with hZ
  set R := (layers adj mate (k + 1)).2 with hR
  set R₀ := (layers adj mate k).2 with hR₀
  have hR₀R : R₀ ⊆ R := layers_snd_mono (Nat.le_succ k)
  have hcover : ∀ p ∈ M, p.1 ∈ Z → p.2 ∈ R := by
    intro p hp hpZ
    by_cases hm : mate p.2 = some p.1
    · exact layers_snd_mono (Nat.le_succ k) (mem_layers_snd_of_mate hv hm hpZ)
    · exact mem_layers_succ_snd.2 ⟨p.1, hpZ, hM.edge p hp, hm⟩
  have h1 : M.card ≤ (Finset.univ \ Z).card + R.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := M) (p := fun p => p.1 ∉ Z)]
    refine Nat.add_le_add (Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_)
      (fun p hp q hq hpq => ?_)) (Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_)
      (fun p hp q hq hpq => ?_))
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
      simp [hp.2]
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      exact hM.left p hp.1 q hq.1 hpq
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, not_not] at hp
      exact Finset.mem_coe.2 (hcover p hp.1 hp.2)
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      exact hM.right p hp.1 q hq.1 hpq
  have h2 : (Finset.univ \ Z).card + R₀.card ≤ (pairs mate).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := pairs mate) (p := fun p => p.1 ∉ Z)]
    refine Nat.add_le_add ((Finset.card_le_card
      (t := ((pairs mate).filter fun p => p.1 ∉ Z).image Prod.fst) fun i hi => ?_).trans
        Finset.card_image_le)
      ((Finset.card_le_card (t := ((pairs mate).filter fun p => ¬ p.1 ∉ Z).image Prod.snd)
        fun j hj => ?_).trans Finset.card_image_le)
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      have hnf : ¬ Free mate i := fun hf =>
        hi (layers_fst_mono (Nat.zero_le k) (mem_layers_zero_fst.2 hf))
      simp only [Free, not_forall, not_not] at hnf
      obtain ⟨j, hj⟩ := hnf
      exact Finset.mem_image.2 ⟨(i, j), by simp [pairs, hj, hi], rfl⟩
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 fun hn => hk j hn (hR₀R hj)
      have hiZ : i ∈ Z := by
        cases k with
        | zero => rw [hR₀, layers_zero_snd] at hj; simp at hj
        | succ k' => exact mem_layers_succ_fst.2 (Or.inr ⟨j, hj, hi⟩)
      exact Finset.mem_image.2 ⟨(i, j), by simp [pairs, hi, hiZ], rfl⟩
  have h3 : R.card = (R \ R₀).card + R₀.card := (Finset.card_sdiff_add_card_eq_card hR₀R).symm
  omega

/-- **The deficit is at most `b / d`** (the counting step of Hopcroft and Karp's bound): if no
unmatched right vertex is reached in the first `d` rounds, then `d` times the deficit of the
current matching against any matching is at most the number of right vertices reached by round
`d`. -/
theorem mul_card_sub_le (hv : Valid adj mate) {M : Finset (Fin a × Fin b)}
    (hM : IsMatching adj M) : ∀ d : ℕ,
    (∀ k < d, ∀ j, mate j = none → j ∉ (layers adj mate (k + 1)).2) →
    d * (M.card - (pairs mate).card) ≤ (layers adj mate d).2.card
  | 0, _ => by simp
  | d + 1, hd => by
      have ih := mul_card_sub_le hv hM d fun k hk => hd k (by omega)
      have hstep := card_le_card_pairs_add hv hM (hd d (Nat.lt_succ_self d))
      have hsub : (layers adj mate d).2 ⊆ (layers adj mate (d + 1)).2 :=
        layers_snd_mono (Nat.le_succ d)
      have h3 := Finset.card_sdiff_add_card_eq_card hsub
      rw [Nat.succ_mul]
      omega

/-- With no phase to run, the matching is maximum and `hopcroftKarpAux` returns it. -/
theorem hopcroftKarpAux_of_hkStep_none (h : hkStep adj mate = none) :
    ∀ f, hopcroftKarpAux adj f mate = mate
  | 0 => rfl
  | f + 1 => by simp [hopcroftKarpAux, h]

/-- Running `f` phases and then `g` more is running `f + g` phases. -/
theorem hopcroftKarpAux_add : ∀ (f g : ℕ) (mate : Fin b → Option (Fin a)),
    hopcroftKarpAux adj (f + g) mate = hopcroftKarpAux adj g (hopcroftKarpAux adj f mate)
  | 0, g, mate => by simp [hopcroftKarpAux]
  | f + 1, g, mate => by
      rw [show f + 1 + g = (f + g) + 1 by omega]
      cases h : hkStep adj mate with
      | none =>
          simp only [hopcroftKarpAux, h]
          exact (hopcroftKarpAux_of_hkStep_none h g).symm
      | some m' =>
          simp only [hopcroftKarpAux, h]
          exact hopcroftKarpAux_add f g m'

/-- **Each phase lengthens the shortest augmenting paths.** After `f` phases from a matching whose
`firstFreeRound` is at least `c`, the `firstFreeRound` is at least `c + f` (or there is none). -/
theorem firstFreeRound_hopcroftKarpAux : ∀ (f c : ℕ) (mate : Fin b → Option (Fin a)),
    Valid adj mate → (∀ d, firstFreeRound adj mate = some d → c ≤ d) →
    Valid adj (hopcroftKarpAux adj f mate) ∧
      ∀ d, firstFreeRound adj (hopcroftKarpAux adj f mate) = some d → c + f ≤ d
  | 0, c, mate, hv, hc => by simpa [hopcroftKarpAux] using ⟨hv, hc⟩
  | f + 1, c, mate, hv, hc => by
      cases h : hkStep adj mate with
      | none =>
          rw [hopcroftKarpAux_of_hkStep_none h]
          refine ⟨hv, fun d hd => absurd hd ?_⟩
          rw [firstFreeRound_eq_none.2 (hkStep_none hv h)]
          simp
      | some m' =>
          simp only [hopcroftKarpAux, h]
          have hv' := (hkStep_some hv h).1
          -- the phase was not empty, so the search reached an unmatched right vertex
          obtain ⟨d₀, hd₀⟩ : ∃ d₀, firstFreeRound adj mate = some d₀ := by
            cases hf : firstFreeRound adj mate with
            | none => simp [hkStep, phase, hf] at h
            | some d₀ => exact ⟨d₀, rfl⟩
          have hm' : m' = flip mate (phase adj mate).flatten := by
            simp only [hkStep] at h
            split_ifs at h
            exact (Option.some.inj h).symm
          have hc' : ∀ d, firstFreeRound adj m' = some d → c + 1 ≤ d := by
            intro d hd
            rw [hm'] at hd
            have := lt_firstFreeRound_flip_phase hv hd₀ hd
            have := hc d₀ hd₀
            omega
          obtain ⟨h1, h2⟩ := firstFreeRound_hopcroftKarpAux f (c + 1) m' hv' hc'
          exact ⟨h1, fun d hd => by have := h2 d hd; omega⟩

/-- Each phase adds an edge until the matching is maximum: if the current matching is within `f`
of a matching `M`, then `f` more phases reach at least `M`'s size. -/
theorem card_le_hopcroftKarpAux_of_le : ∀ (f : ℕ) (mate : Fin b → Option (Fin a)),
    Valid adj mate → ∀ M, IsMatching adj M → M.card ≤ (pairs mate).card + f →
      M.card ≤ (pairs (hopcroftKarpAux adj f mate)).card
  | 0, mate, _, M, _, h => by simpa [hopcroftKarpAux] using h
  | f + 1, mate, hv, M, hM, h => by
      cases hs : hkStep adj mate with
      | none =>
          rw [hopcroftKarpAux_of_hkStep_none hs]
          exact card_le_of_no_free hv (hkStep_none hv hs) hM
      | some m' =>
          simp only [hopcroftKarpAux, hs]
          obtain ⟨hv', hcard⟩ := hkStep_some hv hs
          refine card_le_hopcroftKarpAux_of_le f m' hv' M hM ?_
          rw [card_pairs] at h ⊢
          omega

/-- **Hopcroft and Karp's bound: `2 ⌊√b⌋ + 2` phases suffice.** From the empty matching, after
`2 ⌊√b⌋ + 2` phases the matching is maximum. After the first `⌊√b⌋ + 1` phases every augmenting
path has more than `⌊√b⌋` pairs (`firstFreeRound_hopcroftKarpAux`), so the deficit is at most
`⌊√b⌋` (`mul_card_sub_le`), and each further phase adds an edge. -/
theorem card_le_hopcroftKarpAux_sqrt {M : Finset (Fin a × Fin b)} (hM : IsMatching adj M) :
    M.card ≤ (pairs (hopcroftKarpAux adj (2 * Nat.sqrt b + 2) fun _ => none)).card := by
  set s := Nat.sqrt b with hs
  have hv₀ : Valid adj (fun _ : Fin b => (none : Option (Fin a))) := ⟨by simp, by simp⟩
  rw [show 2 * s + 2 = (s + 1) + (s + 1) by omega, hopcroftKarpAux_add]
  obtain ⟨hv₁, hd₁⟩ := firstFreeRound_hopcroftKarpAux (s + 1) 0 _ hv₀ (fun _ _ => Nat.zero_le _)
  set m₁ := hopcroftKarpAux adj (s + 1) fun _ => none
  refine card_le_hopcroftKarpAux_of_le (s + 1) m₁ hv₁ M hM ?_
  cases hf : firstFreeRound adj m₁ with
  | none =>
      have := card_le_of_no_free hv₁ (firstFreeRound_eq_none.1 hf) hM
      omega
  | some d =>
      have hds : s + 1 ≤ d := by have := hd₁ d hf; omega
      obtain ⟨-, -, hmin⟩ := firstFreeRound_eq_some.1 hf
      have hmul := mul_card_sub_le hv₁ hM d hmin
      have hR : (layers adj m₁ d).2.card ≤ b := by
        simpa using Finset.card_le_univ (layers adj m₁ d).2
      have hsq : b < (s + 1) * (s + 1) := Nat.lt_succ_sqrt b
      have h1 : (s + 1) * (M.card - (pairs m₁).card) ≤ d * (M.card - (pairs m₁).card) :=
        Nat.mul_le_mul_right _ hds
      have h2 : M.card - (pairs m₁).card < s + 1 := by
        by_contra hge
        push Not at hge
        have := Nat.mul_le_mul_left (s + 1) hge
        omega
      omega

end Sqrt

end Cslib.Algorithms.Lean.BipartiteMatching
