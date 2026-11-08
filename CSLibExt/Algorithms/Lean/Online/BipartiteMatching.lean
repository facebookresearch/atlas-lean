/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BipartiteMatching

/-!
# Online bipartite matching: greedy is `1/2`-competitive

Online bipartite matching (Karp, Vazirani and Vazirani, *An optimal algorithm for on-line
bipartite matching*, STOC 1990): the right vertices arrive one at a time with their edges to the
left side, and each must be matched to a free neighbour or left unmatched, irrevocably, on
arrival. The greedy algorithm matches each arriving vertex to its first free neighbour (`step` and
`greedy` specify it, `greedyAll` runs it on arrays, `greedyAll_eq`; the graph and the
`IsMatching`, `Valid`, `pairs` vocabulary are those of `Graph/BipartiteMatching.lean`).

Main results:

* `greedyAll_valid`, `isMatching_greedyAll`: the result is a matching.
* `greedyAll_maximal`: **it is maximal**, every edge has a matched endpoint (`greedy_spec`: the
  invariant of the run, `step_valid`, `step_done`).
* `card_le_two_mul_greedyAll`: **greedy is `1/2`-competitive**, every matching has at most twice
  as many edges; `card_maxMatching_le`: in particular a maximum one.

The factor `2` is tight for greedy: on left vertex `0` adjacent to right `0, 1` and left `1`
adjacent to right `0`, with right `0` arriving first, greedy matches one edge out of two (see the
tests).

## Cost model

The cost is the size of the matching; there is no running-time model. On arrays (`stepArr`,
`greedyArr`), each arrival scans the left vertices once (`List.find?`): for each it tests
`j ∈ adj i` (linear in the length of `adj i`) and `Free`, which scans the right vertices. The run
thus takes `O(a b² + b E)` steps, where `E = ∑ i, (adj i).length`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.BipartiteMatching

open Cslib.Algorithms.Lean.BipartiteMatching

variable {a b : ℕ} (adj : Fin a → List (Fin b))

/-- On the arrival of right vertex `j`, match it to the first free left neighbour, if any. -/
def step (mate : Fin b → Option (Fin a)) (j : Fin b) : Fin b → Option (Fin a) :=
  Function.update mate j
    ((List.finRange a).find? fun i => decide (j ∈ adj i) && decide (Free mate i))

/-- The greedy online matching (specification): right vertices arrive in the order `js`. -/
def greedy (js : List (Fin b)) (mate : Fin b → Option (Fin a)) : Fin b → Option (Fin a) :=
  js.foldl (step adj) mate

/-- Every left vertex matched before a step stays matched with the same partner. -/
theorem step_extends {mate : Fin b → Option (Fin a)} {j : Fin b} (hj : mate j = none)
    {j' : Fin b} {i : Fin a} (h : mate j' = some i) : step adj mate j j' = some i := by
  have : j' ≠ j := fun e => by rw [e, hj] at h; cases h
  simp [step, Function.update_of_ne this, h]

theorem free_of_free_step {mate : Fin b → Option (Fin a)} {j : Fin b} (hj : mate j = none)
    {i : Fin a} (h : Free (step adj mate j) i) : Free mate i :=
  fun j' hj' => h j' (step_extends adj hj hj')

theorem step_valid {mate : Fin b → Option (Fin a)} (hv : Valid adj mate) {j : Fin b}
    (hj : mate j = none) : Valid adj (step adj mate j) := by
  cases hf : (List.finRange a).find? (fun i => decide (j ∈ adj i) && decide (Free mate i)) with
  | none =>
      have : step adj mate j = mate := by
        funext j'
        by_cases h : j' = j
        · subst h; simp [step, hf, hj]
        · simp [step, Function.update_of_ne h]
      rw [this]; exact hv
  | some i₀ =>
      have hi₀ := List.find?_some hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi₀
      have hstep : ∀ j', step adj mate j j' = if j' = j then some i₀ else mate j' := by
        intro j'
        by_cases h : j' = j
        · subst h; simp [step, hf]
        · simp [step, h]
      refine ⟨fun i j' h => ?_, fun i j₁ j₂ h₁ h₂ => ?_⟩
      · rw [hstep] at h
        split_ifs at h with hj'
        · cases h; subst hj'; exact hi₀.1
        · exact hv.edge i j' h
      · rw [hstep] at h₁ h₂
        split_ifs at h₁ h₂ with e₁ e₂ e₂
        · rw [e₁, e₂]
        · cases h₁; exact absurd h₂ (hi₀.2 j₂)
        · cases h₂; exact absurd h₁ (hi₀.2 j₁)
        · exact hv.inj i j₁ j₂ h₁ h₂

/-- Right vertices of `S` are *done*: each is matched, or all its neighbours are matched. -/
def Done (mate : Fin b → Option (Fin a)) (S : List (Fin b)) : Prop :=
  ∀ j ∈ S, ∀ i, j ∈ adj i → mate j ≠ none ∨ ¬ Free mate i

theorem step_done {mate : Fin b → Option (Fin a)} {S : List (Fin b)} (hd : Done adj mate S)
    {j : Fin b} (hj : mate j = none) : Done adj (step adj mate j) (j :: S) := by
  intro j' hj' i hi
  rcases List.mem_cons.1 hj' with rfl | hS
  · cases hf : (List.finRange a).find? (fun i => decide (j' ∈ adj i) && decide (Free mate i)) with
    | some i₀ => left; simp [step, hf]
    | none =>
        right
        intro hfree
        have := List.find?_eq_none.1 hf i (List.mem_finRange i)
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at this
        exact this hi (free_of_free_step adj hj hfree)
  · rcases hd j' hS i hi with h | h
    · left
      obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.1 h
      rw [step_extends adj hj hi']
      exact Option.some_ne_none _
    · right
      exact fun hfree => h (free_of_free_step adj hj hfree)

/-- The invariants of the greedy run: a valid partner array, and every arrived vertex done. -/
theorem greedy_spec : ∀ (js : List (Fin b)) (mate : Fin b → Option (Fin a)) (S : List (Fin b)),
    js.Nodup → (∀ j ∈ js, mate j = none) → Valid adj mate → Done adj mate S →
    Valid adj (greedy adj js mate) ∧ Done adj (greedy adj js mate) (js.reverse ++ S)
  | [], _, _, _, _, hv, hd => ⟨hv, hd⟩
  | j :: js, mate, S, hnd, hfresh, hv, hd => by
      have hj := hfresh j List.mem_cons_self
      have hnd' := (List.nodup_cons.1 hnd)
      have hfresh' : ∀ j' ∈ js, step adj mate j j' = none := fun j' hj' => by
        have hne : j' ≠ j := fun e => hnd'.1 (e ▸ hj')
        simp [step, Function.update_of_ne hne, hfresh j' (List.mem_cons_of_mem _ hj')]
      have := greedy_spec js (step adj mate j) (j :: S) hnd'.2 hfresh' (step_valid adj hv hj)
        (step_done adj hd hj)
      simpa [greedy, List.reverse_cons, List.append_assoc] using this

theorem valid_none : Valid adj (fun _ : Fin b => (none : Option (Fin a))) where
  edge _ _ h := by cases h
  inj _ _ _ h := by cases h

/-! ## The run on arrays -/

/-- A partner array stored as an array. -/
def toFun (arr : Array (Option (Fin a))) : Fin b → Option (Fin a) := fun j => arr.getD j none

/-- One arrival on the array: the same choice as `step`, written into the array. Evaluating the
composed `Function.update`s of `greedy` directly would recompute every earlier choice at each
lookup, a cost exponential in `b`; the array is computed once per arrival. -/
def stepArr (arr : Array (Option (Fin a))) (j : Fin b) : Array (Option (Fin a)) :=
  arr.set! j ((List.finRange a).find? fun i =>
    decide (j ∈ adj i) && decide (Free (toFun (b := b) arr) i))

theorem size_stepArr (arr : Array (Option (Fin a))) (j : Fin b) :
    (stepArr adj arr j).size = arr.size := by
  simp [stepArr]

theorem toFun_stepArr {arr : Array (Option (Fin a))} (h : arr.size = b) (j : Fin b) :
    toFun (stepArr adj arr j) = step adj (toFun arr) j := by
  funext j'
  by_cases hj : j' = j
  · subst hj
    simp [toFun, stepArr, step, h, j'.isLt]
  · have hne : (j : ℕ) ≠ j' := fun e => hj (Fin.ext e).symm
    simp [toFun, stepArr, step, Function.update_of_ne hj, Array.getElem?_setIfInBounds_ne hne]

/-- The greedy run on arrays. -/
def greedyArr (js : List (Fin b)) (arr : Array (Option (Fin a))) : Array (Option (Fin a)) :=
  js.foldl (stepArr adj) arr

theorem toFun_greedyArr : ∀ (js : List (Fin b)) {arr : Array (Option (Fin a))}, arr.size = b →
    toFun (greedyArr adj js arr) = greedy adj js (toFun arr)
  | [], _, _ => rfl
  | j :: js, arr, h => by
      simp only [greedyArr, greedy, List.foldl_cons] at *
      rw [← toFun_stepArr adj h j]
      exact toFun_greedyArr js (by rw [size_stepArr]; exact h)

/-- The greedy matching after all `b` right vertices arrive in order, computed on arrays. -/
def greedyAll : Fin b → Option (Fin a) :=
  toFun (greedyArr adj (List.finRange b) (Array.replicate b none))

theorem greedyAll_eq : greedyAll adj = greedy adj (List.finRange b) fun _ => none := by
  rw [greedyAll, toFun_greedyArr adj _ (Array.size_replicate)]
  congr 1
  funext j
  simp [toFun, j.isLt]

theorem greedyAll_valid : Valid adj (greedyAll adj) := by
  rw [greedyAll_eq]
  exact (greedy_spec adj _ _ [] (List.nodup_finRange b) (fun _ _ => rfl)
    (valid_none adj) (fun _ h => absurd h List.not_mem_nil)).1

/-- **The greedy matching is maximal**: every edge has a matched endpoint. -/
theorem greedyAll_maximal {i : Fin a} {j : Fin b} (h : j ∈ adj i) :
    greedyAll adj j ≠ none ∨ ¬ Free (greedyAll adj) i := by
  rw [greedyAll_eq]
  have := (greedy_spec adj _ _ [] (List.nodup_finRange b) (fun _ _ => rfl)
    (valid_none adj) (fun _ h => absurd h List.not_mem_nil)).2
  exact this j (by simp) i h

/-- **Greedy online matching is `1/2`-competitive**: every matching has at most twice as many
edges as the greedy one. An edge of the matching whose right vertex the greedy algorithm matched
is charged to that right vertex, any other edge to its left vertex, which the greedy algorithm
matched by maximality; a matching charges each greedy edge at most once on each side. -/
theorem card_le_two_mul_greedyAll {M : Finset (Fin a × Fin b)} (hM : IsMatching adj M) :
    M.card ≤ 2 * (pairs (greedyAll adj)).card := by
  set g := greedyAll adj
  set G := pairs g
  have hsplit := Finset.card_filter_add_card_filter_not (s := M) (p := fun q => g q.2 ≠ none)
  -- edges with a greedy-matched right vertex: injective on right vertices
  have h1 : (M.filter fun q => g q.2 ≠ none).card ≤ G.card := by
    calc (M.filter fun q => g q.2 ≠ none).card
        = ((M.filter fun q => g q.2 ≠ none).image Prod.snd).card :=
          (Finset.card_image_of_injOn fun p hp q hq h =>
            hM.right p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 h).symm
      _ ≤ (G.image Prod.snd).card := Finset.card_le_card fun j hj => by
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hj
          obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.1 (Finset.mem_filter.1 hq).2
          exact Finset.mem_image.2 ⟨(i', q.2), by simp [G, pairs, hi'], rfl⟩
      _ ≤ G.card := Finset.card_image_le
  -- the other edges: their left vertex is greedy-matched; injective on left vertices
  have h2 : (M.filter fun q => ¬ g q.2 ≠ none).card ≤ G.card := by
    calc (M.filter fun q => ¬ g q.2 ≠ none).card
        = ((M.filter fun q => ¬ g q.2 ≠ none).image Prod.fst).card :=
          (Finset.card_image_of_injOn fun p hp q hq h =>
            hM.left p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 h).symm
      _ ≤ (G.image Prod.fst).card := Finset.card_le_card fun i hi => by
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
          obtain ⟨hqM, hnone⟩ := Finset.mem_filter.1 hq
          have hmax := greedyAll_maximal adj (hM.edge q hqM)
          have hnf : ¬ Free g q.1 := hmax.resolve_left hnone
          unfold Free at hnf
          push Not at hnf
          obtain ⟨j', hj'⟩ := hnf
          exact Finset.mem_image.2 ⟨(q.1, j'), by simp [G, pairs, hj'], rfl⟩
      _ ≤ G.card := Finset.card_image_le
  omega

/-- The greedy matching is a matching. -/
theorem isMatching_greedyAll : IsMatching adj (pairs (greedyAll adj)) :=
  isMatching_pairs (greedyAll_valid adj)

/-- Against the optimum: a maximum matching (`maxMatching`) has at most twice as many edges as
the greedy online matching. -/
theorem card_maxMatching_le : (pairs (maxMatching adj)).card ≤ 2 * (pairs (greedyAll adj)).card :=
  card_le_two_mul_greedyAll adj isMatching_maxMatching

end Cslib.Algorithms.Lean.Online.BipartiteMatching
