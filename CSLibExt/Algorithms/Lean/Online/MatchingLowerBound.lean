/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BipartiteMatching
public import CSLibExt.Algorithms.Lean.Online.BipartiteMatching
public import Mathlib.Data.List.Forall2

/-!
# No deterministic online bipartite matching algorithm beats `1/2`

Online bipartite matching (Karp, Vazirani and Vazirani, *An optimal algorithm for on-line
bipartite matching*, STOC 1990): right vertices arrive one at a time with their lists of left
neighbours and are matched irrevocably on arrival. The greedy algorithm is `1/2`-competitive;
this module proves that no deterministic algorithm does better, the observation that motivates
randomized algorithms such as KVV's RANKING.

The model: an `OnlineMatcher` proposes a left vertex for each arrival from the neighbour lists
seen so far (`choose`); `matched` runs it, accepting a proposal when it is a free neighbour.
`IsPerfect σ m` says `m` matches every arrival of `σ` to a distinct neighbour; by
`exists_isMatching_of_isPerfect` it is a matching (`BipartiteMatching.IsMatching`) with one edge
per arrival of the arrivals' graph `toAdj σ`.

Main results:

* `adversary`: on each gadget `(u, v)`, an arrival adjacent to `u` and `v`, then one adjacent
  only to `v` if the algorithm proposed `v` for it, and only to `u` otherwise (a proposal of `u`,
  of nothing, or of a non-neighbour). `matched_adversary_le`: every algorithm
  matches at most one arrival per gadget; `isPerfect_adversaryOpt`: the arrivals have a perfect
  matching when the gadgets have distinct vertices (`GadgetsDisjoint`).
* `exists_perfect_matched_le`: against every algorithm with `2 n` left vertices, some `2 n`
  arrivals have a perfect matching while the algorithm matches at most `n`
  (`exists_isMatching_matched_le`: the same with a `BipartiteMatching.IsMatching`);
  `not_competitive_of_lt`: so for `d < 2 * c` and `b < n`, `d * ALG + b < c * OPT` on some
  sequence (a finite-size obstruction); `not_competitive`: for a family of algorithms, one per
  size, every additive constant `b` fails at some size.
* `greedyMatcher`: the greedy algorithm of `Online/BipartiteMatching.lean` as an `OnlineMatcher`;
  `matched_greedyMatcher_eq_card`: it matches as many arrivals as `greedyAll` has edges on the
  arrivals' graph `toAdj σ`, so `card_le_two_mul_matched_greedyMatcher` carries greedy's `1/2`
  bound into this model, and `greedy_tight`: greedy matches exactly half of a perfect matching on
  the adversary's arrivals, so it attains the best ratio a deterministic algorithm can.

## Cost model

The cost is the number of matched arrivals; there is no computation to charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.MatchingLowerBound

/-- A deterministic online bipartite matching algorithm with `a` offline (left) vertices: on each
arrival it sees the neighbour lists of all earlier arrivals and of the current one, and proposes a
left vertex to match the arrival to, or none. -/
structure OnlineMatcher (a : ℕ) where
  /-- The proposal for the current arrival, from the earlier arrivals and the current one. -/
  choose : List (List (Fin a)) → List (Fin a) → Option (Fin a)

variable {a : ℕ}

/-- The run of `A` on the arrivals `σ` (neighbour lists), after the history `h` and with the left
vertices `used` already matched: the number of arrivals matched. A proposal is accepted when it
is a neighbour of the arrival and still free; otherwise the arrival stays unmatched. -/
def matched (A : OnlineMatcher a) : List (List (Fin a)) → List (Fin a) → List (List (Fin a)) → ℕ
  | _, _, [] => 0
  | h, used, nbrs :: σ =>
      match A.choose h nbrs with
      | some i =>
          if i ∈ nbrs ∧ i ∉ used then 1 + matched A (h ++ [nbrs]) (i :: used) σ
          else matched A (h ++ [nbrs]) used σ
      | none => matched A (h ++ [nbrs]) used σ

/-- `m` matches the arrivals `σ` (in order) to distinct neighbours: a matching that covers every
arrival. -/
def IsPerfect (σ : List (List (Fin a))) (m : List (Fin a)) : Prop :=
  m.Nodup ∧ List.Forall₂ (fun i nbrs => i ∈ nbrs) m σ

/-- The bipartite graph of a sequence of arrivals, in the vocabulary of
`Graph/BipartiteMatching.lean`: left vertex `i` is adjacent to arrival `j` when `i ∈ σ[j]`. -/
def toAdj (σ : List (List (Fin a))) : Fin a → List (Fin σ.length) :=
  fun i => (List.finRange σ.length).filter fun j => decide (i ∈ σ[j])

/-- A perfect matching of the arrivals is a matching (`BipartiteMatching.IsMatching`) of their
graph with one edge per arrival. -/
theorem exists_isMatching_of_isPerfect {σ : List (List (Fin a))} {m : List (Fin a)}
    (hp : IsPerfect σ m) : ∃ M : Finset (Fin a × Fin σ.length),
      BipartiteMatching.IsMatching (toAdj σ) M ∧ M.card = σ.length := by
  obtain ⟨hnd, hf⟩ := hp
  have hlen : m.length = σ.length := hf.length_eq
  let e : Fin σ.length → Fin a × Fin σ.length := fun j => (m[j.1]'(by rw [hlen]; exact j.isLt), j)
  have he : Function.Injective e := fun j j' h => (Prod.mk.inj h).2
  refine ⟨Finset.univ.image e, ⟨fun p hp => ?_, fun p hp q hq h => ?_, fun p hp q hq h => ?_⟩,
    by rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]⟩
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    simp only [toAdj, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and, e]
    exact hf.get (by rw [hlen]; exact j.isLt) j.isLt
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hq
    have : j.1 = j'.1 := (hnd.getElem_inj_iff).1 h
    rw [Fin.ext this]
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hq
    rw [show j = j' from h]

/-! ## The adversary -/

/-- The adversary on gadgets `(u, v)`: an arrival adjacent to `u` and `v`, then an arrival
adjacent only to `v` if the algorithm proposed `v` for the first one, and only to `u` otherwise
(a proposal of `u`, of no vertex, or of a non-neighbour). -/
def adversary (A : OnlineMatcher a) : List (List (Fin a)) → List (Fin a × Fin a) →
    List (List (Fin a))
  | _, [] => []
  | h, (u, v) :: ps =>
      let x := if A.choose h [u, v] = some v then v else u
      [u, v] :: [x] :: adversary A (h ++ [[u, v], [x]]) ps

/-- The offline matching of the adversary's arrivals: in each gadget, the first arrival takes the
vertex the second one does not. -/
def adversaryOpt (A : OnlineMatcher a) : List (List (Fin a)) → List (Fin a × Fin a) → List (Fin a)
  | _, [] => []
  | h, (u, v) :: ps =>
      let x := if A.choose h [u, v] = some v then v else u
      (if A.choose h [u, v] = some v then u else v) :: x :: adversaryOpt A (h ++ [[u, v], [x]]) ps

/-- Gadgets with distinct vertices: within each gadget, and across gadgets. -/
def GadgetsDisjoint (ps : List (Fin a × Fin a)) : Prop :=
  (∀ p ∈ ps, p.1 ≠ p.2) ∧
    ps.Pairwise fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

theorem length_adversary (A : OnlineMatcher a) : ∀ (h : List (List (Fin a)))
    (ps : List (Fin a × Fin a)), (adversary A h ps).length = 2 * ps.length
  | _, [] => rfl
  | h, (u, v) :: ps => by
      simp only [adversary, List.length_cons, length_adversary A _ ps]
      omega

/-- **The adversary holds every algorithm to one match per gadget.** -/
theorem matched_adversary_le (A : OnlineMatcher a) : ∀ (h : List (List (Fin a)))
    (used : List (Fin a)) (ps : List (Fin a × Fin a)),
    matched A h used (adversary A h ps) ≤ ps.length
  | _, _, [] => by simp [adversary, matched]
  | h, used, (u, v) :: ps => by
      set h₂ := h ++ [[u, v], [if A.choose h [u, v] = some v then v else u]] with hh₂
      have ih : ∀ used', matched A h₂ used' (adversary A h₂ ps) ≤ ps.length :=
        fun used' => matched_adversary_le A h₂ used' ps
      simp only [adversary, matched, List.length_cons]
      have happ : h ++ [[u, v]] ++ [[if A.choose h [u, v] = some v then v else u]] = h₂ := by
        simp [hh₂]
      rw [happ, ← hh₂]
      clear_value h₂
      have k1 : ∀ U, matched A h₂ U (adversary A h₂ ps) ≤ ps.length + 1 :=
        fun U => Nat.le_succ_of_le (ih U)
      have k2 : ∀ U, 1 + matched A h₂ U (adversary A h₂ ps) ≤ ps.length + 1 :=
        fun U => by have := ih U; omega
      cases hc : A.choose h [u, v] with
      | none =>
          simp only [reduceCtorEq, ↓reduceIte]
          split <;> (try split_ifs) <;> first | exact k1 _ | exact k2 _
      | some i =>
          by_cases hiv : i = v
          · subst hiv
            simp only [↓reduceIte]
            split_ifs with h1
            · split
              · split_ifs with h2
                · exact absurd (List.mem_cons.2 (Or.inl (List.mem_singleton.1 h2.1))) h2.2
                · exact k2 _
              · exact k2 _
            · split <;> (try split_ifs) <;> first | exact k1 _ | exact k2 _
          · have hne' : (some i = some v) = False := by simp [hiv]
            simp only [hne', ↓reduceIte]
            split_ifs with h1
            · have hiu : i = u := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
                tauto
              subst hiu
              split
              · split_ifs with h2
                · exact absurd (List.mem_cons.2 (Or.inl (List.mem_singleton.1 h2.1))) h2.2
                · exact k2 _
              · exact k2 _
            · split <;> (try split_ifs) <;> first | exact k1 _ | exact k2 _

theorem mem_adversaryOpt (A : OnlineMatcher a) : ∀ (h : List (List (Fin a)))
    (ps : List (Fin a × Fin a)) (x : Fin a), x ∈ adversaryOpt A h ps →
    ∃ q ∈ ps, x = q.1 ∨ x = q.2
  | _, [], _, hx => by simp [adversaryOpt] at hx
  | h, (u, v) :: ps, x, hx => by
      simp only [adversaryOpt, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · refine ⟨(u, v), List.mem_cons_self, ?_⟩
        split_ifs at hx <;> simp [hx]
      · refine ⟨(u, v), List.mem_cons_self, ?_⟩
        split_ifs at hx <;> simp [hx]
      · obtain ⟨q, hq, hxq⟩ := mem_adversaryOpt A _ ps x hx
        exact ⟨q, List.mem_cons_of_mem _ hq, hxq⟩

/-- **The adversary's arrivals have a perfect matching** when the gadgets have distinct vertices:
in each gadget the first arrival takes the vertex the second one does not. -/
theorem isPerfect_adversaryOpt (A : OnlineMatcher a) : ∀ (h : List (List (Fin a)))
    (ps : List (Fin a × Fin a)), GadgetsDisjoint ps →
    IsPerfect (adversary A h ps) (adversaryOpt A h ps)
  | _, [], _ => ⟨List.nodup_nil, List.Forall₂.nil⟩
  | h, (u, v) :: ps, ⟨hne, hpw⟩ => by
      have huv : u ≠ v := hne (u, v) List.mem_cons_self
      have hd' : GadgetsDisjoint ps := ⟨fun p hp => hne p (List.mem_cons_of_mem _ hp),
        (List.pairwise_cons.1 hpw).2⟩
      obtain ⟨hnd, hf⟩ := isPerfect_adversaryOpt A (h ++ [[u, v],
        [if A.choose h [u, v] = some v then v else u]]) ps hd'
      have hfar : ∀ x ∈ adversaryOpt A (h ++ [[u, v],
          [if A.choose h [u, v] = some v then v else u]]) ps, x ≠ u ∧ x ≠ v := by
        intro x hx
        obtain ⟨q, hq, hxq⟩ := mem_adversaryOpt A _ ps x hx
        have := (List.pairwise_cons.1 hpw).1 q hq
        simp only at this
        rcases hxq with rfl | rfl <;> exact ⟨fun e => by simp_all, fun e => by simp_all⟩
      simp only [IsPerfect, adversaryOpt, adversary]
      refine ⟨?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hnd⟩⟩
        · simp only [List.mem_cons, not_or]
          refine ⟨by split_ifs <;> simp [huv, huv.symm], fun hx => ?_⟩
          have := hfar _ hx
          split_ifs at this <;> simp_all
        · intro hx
          have := hfar _ hx
          split_ifs at this <;> simp_all
      · refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ hf)
        · split_ifs <;> simp
        · simp

/-- `n` gadgets on the left vertices `2k, 2k + 1` of `Fin (2 * n)`. -/
def gadgets (n : ℕ) : List (Fin (2 * n) × Fin (2 * n)) :=
  (List.finRange n).map fun (k : Fin n) =>
    (⟨2 * k, by have := k.isLt; omega⟩, ⟨2 * k + 1, by have := k.isLt; omega⟩)

theorem gadgetsDisjoint_gadgets (n : ℕ) : GadgetsDisjoint (gadgets n) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    simp [Fin.ext_iff]
  · refine List.Pairwise.map _ (fun k k' hkk' => ?_) (List.nodup_finRange n)
    have : (k : ℕ) ≠ k' := fun e => hkk' (Fin.ext e)
    simp only [ne_eq, Fin.mk.injEq]
    omega

theorem length_gadgets (n : ℕ) : (gadgets n).length = n := by simp [gadgets]

/-- **No deterministic online bipartite matching algorithm beats `1/2`** (Karp, Vazirani and
Vazirani): against every algorithm with `2 n` left vertices, some sequence of `2 n` arrivals has
a perfect matching while the algorithm matches at most `n` of them. -/
theorem exists_perfect_matched_le (n : ℕ) (A : OnlineMatcher (2 * n)) :
    ∃ σ m, IsPerfect σ m ∧ m.length = 2 * n ∧ σ.length = 2 * n ∧ matched A [] [] σ ≤ n := by
  refine ⟨adversary A [] (gadgets n), adversaryOpt A [] (gadgets n),
    isPerfect_adversaryOpt A [] _ (gadgetsDisjoint_gadgets n), ?_, ?_, ?_⟩
  · have := (isPerfect_adversaryOpt A [] _ (gadgetsDisjoint_gadgets n)).2.length_eq
    rw [this, length_adversary, length_gadgets]
  · rw [length_adversary, length_gadgets]
  · simpa [length_gadgets] using matched_adversary_le A [] [] (gadgets n)

/-- The same in the vocabulary of `Graph/BipartiteMatching.lean`: the arrivals' graph has a
matching (`BipartiteMatching.IsMatching`) with `2 n` edges. -/
theorem exists_isMatching_matched_le (n : ℕ) (A : OnlineMatcher (2 * n)) :
    ∃ σ : List (List (Fin (2 * n))), ∃ M : Finset (Fin (2 * n) × Fin σ.length),
      BipartiteMatching.IsMatching (toAdj σ) M ∧ M.card = 2 * n ∧ matched A [] [] σ ≤ n := by
  obtain ⟨σ, m, hm, -, hσ, hle⟩ := exists_perfect_matched_le n A
  obtain ⟨M, hM, hc⟩ := exists_isMatching_of_isPerfect hm
  exact ⟨σ, M, hM, hc.trans hσ, hle⟩

/-- **The finite-size obstruction**: if `d < 2 * c` and `b < n`, every algorithm with `2 n` left
vertices has a sequence with a perfect matching `m` on which `d * ALG + b < c * |m|`. (At a fixed
size some additive constant always suffices, so `b` is bounded by `n`; `not_competitive` lets the
size grow.) -/
theorem not_competitive_of_lt (n : ℕ) {c d : ℕ} (hcd : d < 2 * c) {b : ℕ} (hb : b < n)
    (A : OnlineMatcher (2 * n)) :
    ∃ σ m, IsPerfect σ m ∧ d * matched A [] [] σ + b < c * m.length := by
  obtain ⟨σ, m, hm, hml, -, hle⟩ := exists_perfect_matched_le n A
  refine ⟨σ, m, hm, ?_⟩
  rw [hml]
  have h1 : d * matched A [] [] σ ≤ d * n := Nat.mul_le_mul_left d hle
  have h2 : (d + 1) * n ≤ 2 * c * n := Nat.mul_le_mul_right n hcd
  calc d * matched A [] [] σ + b ≤ d * n + b := by omega
    _ < (d + 1) * n := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ 2 * c * n := h2
    _ = c * (2 * n) := by rw [Nat.mul_comm 2 c, Nat.mul_assoc]

/-- **No deterministic online matcher beats ratio `1/2`, with any additive constant**: for a
family of algorithms, one for each even number `2 n` of left vertices, and all `c d b` with
`d < 2 * c`, some size and some sequence with a perfect matching `m` give
`d * ALG + b < c * |m|`; for `0 < d`, the family is not `c / d`-competitive. -/
theorem not_competitive (A : ∀ n, OnlineMatcher (2 * n)) {c d : ℕ} (hcd : d < 2 * c) (b : ℕ) :
    ∃ n σ m, IsPerfect σ m ∧ d * matched (A n) [] [] σ + b < c * m.length :=
  ⟨b + 1, not_competitive_of_lt (b + 1) hcd (Nat.lt_succ_self b) (A (b + 1))⟩

/-! ## Greedy as an online matcher -/

/-- Greedy's proposal: the free left neighbour of least index, if any. -/
def greedyPick (used nbrs : List (Fin a)) : Option (Fin a) :=
  (List.finRange a).find? fun i => decide (i ∈ nbrs) && decide (i ∉ used)

/-- The left vertices the greedy algorithm has matched after the arrivals `h`. -/
def greedyUsed (h : List (List (Fin a))) : List (Fin a) :=
  h.foldl (fun used nbrs => match greedyPick used nbrs with
    | some i => i :: used
    | none => used) []

/-- **Greedy as an online matcher**: it replays the history to recover the left vertices it has
already matched (`greedyUsed`) and proposes the free neighbour of least index (`greedyPick`), the
choice of `Online.BipartiteMatching.step`. -/
def greedyMatcher : OnlineMatcher a := ⟨fun h nbrs => greedyPick (greedyUsed h) nbrs⟩

private theorem greedyUsed_append_singleton (h : List (List (Fin a))) (nbrs : List (Fin a)) :
    greedyUsed (h ++ [nbrs]) = match greedyPick (greedyUsed h) nbrs with
      | some i => i :: greedyUsed h
      | none => greedyUsed h := by
  simp [greedyUsed, List.foldl_append]

private theorem matched_greedyMatcher_aux : ∀ (σ h : List (List (Fin a))),
    matched greedyMatcher h (greedyUsed h) σ + (greedyUsed h).length =
      (greedyUsed (h ++ σ)).length
  | [], h => by simp [matched]
  | nbrs :: σ, h => by
      have ih := matched_greedyMatcher_aux σ (h ++ [nbrs])
      rw [greedyUsed_append_singleton] at ih
      rw [show h ++ nbrs :: σ = h ++ [nbrs] ++ σ by simp]
      simp only [matched]
      change (match greedyPick (greedyUsed h) nbrs with
        | some i => if i ∈ nbrs ∧ i ∉ greedyUsed h then
            1 + matched greedyMatcher (h ++ [nbrs]) (i :: greedyUsed h) σ
            else matched greedyMatcher (h ++ [nbrs]) (greedyUsed h) σ
        | none => matched greedyMatcher (h ++ [nbrs]) (greedyUsed h) σ) + _ = _
      cases hc : greedyPick (greedyUsed h) nbrs with
      | none => rw [hc] at ih; simpa using ih
      | some i =>
          rw [hc] at ih
          have hi := List.find?_some hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
          simp only [hi, not_false_eq_true, and_self, ↓reduceIte]
          simp only [List.length_cons] at ih
          omega

/-- `greedyMatcher` matches one arrival per left vertex it records as used. -/
theorem matched_greedyMatcher (σ : List (List (Fin a))) :
    matched greedyMatcher [] [] σ = (greedyUsed σ).length := by
  simpa [greedyUsed] using matched_greedyMatcher_aux σ []

open Cslib.Algorithms.Lean.BipartiteMatching in
/-- The invariant of the run of `greedyAll` on the arrivals' graph after the first `k` arrivals:
later arrivals are unmatched, and the free left vertices and the matching size agree with
`greedyUsed`. -/
private theorem greedy_take_inv (σ : List (List (Fin a))) : ∀ k, k ≤ σ.length →
    let mate := Online.BipartiteMatching.greedy (toAdj σ) ((List.finRange σ.length).take k)
      (fun _ => none)
    (∀ j : Fin σ.length, k ≤ j.1 → mate j = none) ∧
    (∀ i, Free mate i ↔ i ∉ greedyUsed (σ.take k)) ∧
    (pairs mate).card = (greedyUsed (σ.take k)).length
  | 0, _ => by
      refine ⟨fun _ _ => rfl, fun i => ?_, ?_⟩
      · simp [greedyUsed, Online.BipartiteMatching.greedy, Free]
      · simp [greedyUsed, Online.BipartiteMatching.greedy, pairs]
  | k + 1, hk => by
      obtain ⟨h1, h2, h3⟩ := greedy_take_inv σ k (by omega)
      intro mate
      set m := Online.BipartiteMatching.greedy (toAdj σ) ((List.finRange σ.length).take k)
        (fun _ => none) with hm
      set used := greedyUsed (σ.take k) with hused
      let j : Fin σ.length := ⟨k, by omega⟩
      have hmj : m j = none := h1 j le_rfl
      have htake : (List.finRange σ.length).take (k + 1) =
          (List.finRange σ.length).take k ++ [j] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
        simp [j]
      have hσ : σ.take (k + 1) = σ.take k ++ [σ[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hpred : (fun i => decide (j ∈ toAdj σ i) && decide (Free m i)) =
          fun i => decide (i ∈ σ[k]) && decide (i ∉ used) := by
        funext i
        simp [toAdj, h2 i, j]
      have hc : (List.finRange a).find? (fun i => decide (j ∈ toAdj σ i) && decide (Free m i)) =
          greedyPick used σ[k] := by
        rw [hpred]; rfl
      have hmate : mate = Function.update m j (greedyPick used σ[k]) := by
        simp only [mate, htake, Online.BipartiteMatching.greedy, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        change Online.BipartiteMatching.step (toAdj σ) m j = _
        simp only [Online.BipartiteMatching.step, hc]
      have hU : greedyUsed (σ.take (k + 1)) = match greedyPick used σ[k] with
          | some i => i :: used
          | none => used := by
        rw [hσ, greedyUsed_append_singleton]
      rw [hmate, hU]
      refine ⟨fun j' hj' => ?_, fun i => ?_, ?_⟩
      · have hne : j' ≠ j := fun e => by have := congrArg Fin.val e; simp only [j] at this; omega
        rw [Function.update_of_ne hne]
        exact h1 j' (by omega)
      · have hfree : Free (Function.update m j (greedyPick used σ[k])) i ↔
            greedyPick used σ[k] ≠ some i ∧ Free m i := by
          constructor
          · intro hf
            refine ⟨fun e => hf j (by simp [e]), fun j' => ?_⟩
            by_cases hj' : j' = j
            · rw [hj', hmj]; simp
            · have := hf j'
              rwa [Function.update_of_ne hj'] at this
          · rintro ⟨hne, hf⟩ j'
            by_cases hj' : j' = j
            · rw [hj', Function.update_self]; exact hne
            · rw [Function.update_of_ne hj']; exact hf j'
        rw [hfree, h2 i]
        cases greedyPick used σ[k] with
        | none => simp
        | some i₀ =>
            simp only [ne_eq, Option.some.injEq, List.mem_cons, not_or]
            tauto
      · cases hg : greedyPick used σ[k] with
        | none =>
            have : Function.update m j none = m := by
              rw [Function.update_eq_self_iff]; exact hmj.symm
            rw [this]; exact h3
        | some i₀ =>
            have hnot : (i₀, j) ∉ pairs m := by simp [pairs, hmj]
            have : pairs (Function.update m j (some i₀)) = insert (i₀, j) (pairs m) := by
              ext ⟨i, j'⟩
              by_cases hj' : j' = j
              · subst hj'
                simp [pairs, hmj, eq_comm]
              · simp [pairs, hj']
            rw [this, Finset.card_insert_of_notMem hnot, h3, List.length_cons]

open Cslib.Algorithms.Lean.BipartiteMatching in
/-- **`greedyMatcher` is the greedy algorithm of `Online/BipartiteMatching.lean`**: on every arrival
sequence it matches as many arrivals as `greedyAll` has edges on the arrivals' graph. -/
theorem matched_greedyMatcher_eq_card (σ : List (List (Fin a))) :
    matched greedyMatcher [] [] σ =
      (pairs (Online.BipartiteMatching.greedyAll (toAdj σ))).card := by
  have := (greedy_take_inv σ σ.length le_rfl).2.2
  rw [List.take_length, List.take_of_length_le (by simp)] at this
  rw [matched_greedyMatcher, Online.BipartiteMatching.greedyAll_eq, this]

/-- **Greedy is `1/2`-competitive in the `OnlineMatcher` model**: every matching of the arrivals'
graph has at most twice as many edges as `greedyMatcher` matches arrivals
(`Online.BipartiteMatching.card_le_two_mul_greedyAll` through `matched_greedyMatcher_eq_card`). -/
theorem card_le_two_mul_matched_greedyMatcher {σ : List (List (Fin a))}
    {M : Finset (Fin a × Fin σ.length)} (hM : BipartiteMatching.IsMatching (toAdj σ) M) :
    M.card ≤ 2 * matched greedyMatcher [] [] σ := by
  rw [matched_greedyMatcher_eq_card]
  exact Online.BipartiteMatching.card_le_two_mul_greedyAll (toAdj σ) hM

/-- The same against a perfect matching of the arrivals: `|m| ≤ 2 * ALG`. -/
theorem length_le_two_mul_matched_greedyMatcher {σ : List (List (Fin a))} {m : List (Fin a)}
    (hm : IsPerfect σ m) : m.length ≤ 2 * matched greedyMatcher [] [] σ := by
  obtain ⟨M, hM, hc⟩ := exists_isMatching_of_isPerfect hm
  rw [hm.2.length_eq, ← hc]
  exact card_le_two_mul_matched_greedyMatcher hM

/-- **The ratio `1/2` is tight for greedy, and greedy is optimal among deterministic online
matchers**: `length_le_two_mul_matched_greedyMatcher` and, from the adversary of
`exists_perfect_matched_le`, for every `n` some `2 n` arrivals have a perfect matching `m` of
which `greedyMatcher` matches exactly half. -/
theorem greedy_tight (n : ℕ) : ∃ σ m, IsPerfect σ m ∧ m.length = 2 * n ∧
    2 * matched (greedyMatcher (a := 2 * n)) [] [] σ = m.length := by
  obtain ⟨σ, m, hm, hml, -, hle⟩ := exists_perfect_matched_le n greedyMatcher
  have := length_le_two_mul_matched_greedyMatcher hm
  exact ⟨σ, m, hm, hml, by omega⟩

end Cslib.Algorithms.Lean.Online.MatchingLowerBound
