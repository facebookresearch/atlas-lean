/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.KnuthMoore
public import CSLibExt.Crypto.Framework.Oracle
public import Mathlib.Data.Finset.Card

/-!
# Knuth and Moore's lower bound: alpha-beta is optimal on perfectly ordered trees

Knuth and Moore (*An analysis of alpha-beta pruning*, Artificial Intelligence 6 (1975)) show
that on a uniform tree of branching factor `k` and depth `d`, every algorithm that determines the
minimax value examines at least `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` leaves, the number alpha-beta
evaluates when the moves are perfectly ordered (`alphaBeta_leafCount_perfect`). This file proves
that bound for adaptive leaf-query algorithms.

## The model

A tree *shape* `s : GameTree ι` carries a variable `i : ι` at every leaf; an input `f : ι → α`
assigns the leaf values, giving the game tree `s.map f`. An algorithm is an adaptive oracle
algorithm `T : OracleComp ι α α` (the Atlas oracle-computation model of
`CSLibExt.Crypto.Framework.Oracle`, CSLib's free monad over one oracle) whose oracle is the input
`f`: it asks for the values of leaves one at a time, each choice depending on the answers so far,
and then outputs a value. It is *correct* for player `p` when `T.run f = minimax p (s.map f)` for
every input `f`, leaves valued `⊥` or `⊤` included (the proof uses two such inputs). The algorithm
may be arbitrary otherwise; it may query a leaf twice, and the bound counts the distinct leaves it
reads, `(T.queries f).toFinset.card`. The only property of the model the bound uses is locality
(`OracleComp.run_congr`): an input that agrees with `f` on the leaves read on input `f` gets the
same output.

## Main results

* `minimax_certificate_lower`: on a uniform shape with distinct leaf variables, a set `Q` of leaves
  whose values determine the minimax value at `f` (every input agreeing with `f` on `Q` has the
  same value) has at least `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` elements, provided the value lies
  strictly between `⊥` and `⊤`.
* `minimax_queries_lower`: every correct query algorithm reads at least that many distinct leaves
  on every such input.
* `alphaBetaQuery`: the Atlas `alphaBeta` written as a query algorithm, which queries the leaves
  `alphaBeta` evaluates, in the same order (`run_alphaBetaQuery`,
  `length_queries_alphaBetaQuery`); it is correct with the full window.
* `alphaBetaQuery_optimal`: on a perfectly ordered input, alpha-beta reads no more leaves than any
  correct query algorithm reads on that input.

The bound holds on every input whose value lies strictly between `⊥` and `⊤`, not only on a
perfectly ordered one, and ties between leaf values are allowed. The value hypothesis is needed:
a root valued `⊤` is certified by the maximizer's strategy alone (the tests show two leaves for
`k = d = 2`).

## Proof

Let `Q` determine the value `v` at `f`. Setting every leaf outside `Q` to `⊥` gives an input
`lo`, setting them to `⊤` an input `hi`; both agree with `f` on `Q`, so both have value `v`. By
induction on the depth, with the node types of Knuth and Moore:

* if the value under `lo` is above `⊥`, `Q` holds a strategy of the maximizer (one child at its
  nodes, every child at the minimizer's), `k ^ ⌊d / 2⌋` leaves when the maximizer moves at the
  root and `k ^ ⌈d / 2⌉` otherwise (`cutLeaves_le_of_bot_lt`);
* dually, if the value under `hi` is below `⊤`, `Q` holds a strategy of the minimizer
  (`cutLeaves_le_of_lt_top`);
* at a principal node (both values equal `v`), some child attains `v` under both inputs and is
  again principal, and every other child is a cut node: this gives the recurrence of `pvLeaves`
  (`pvLeaves_le_countP`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean Cslib.Crypto.Framework

universe u v

variable {ι : Type u} {α : Type v}

/-! ## Game trees whose leaves are variables -/

mutual
/-- Replace the variable `i` at every leaf of a shape by its value `f i`. -/
def GameTree.map (f : ι → α) : GameTree ι → GameTree α
  | .leaf i => .leaf (f i)
  | .node ts => .node (GameTree.mapList f ts)

/-- `GameTree.map` on each tree of a list. -/
def GameTree.mapList (f : ι → α) : List (GameTree ι) → List (GameTree α)
  | [] => []
  | t :: ts => GameTree.map f t :: GameTree.mapList f ts
end

theorem GameTree.mapList_eq (f : ι → α) :
    ∀ ts : List (GameTree ι), GameTree.mapList f ts = ts.map (GameTree.map f)
  | [] => rfl
  | t :: ts => by rw [GameTree.mapList, GameTree.mapList_eq f ts, List.map_cons]

@[simp] theorem GameTree.map_leaf (f : ι → α) (i : ι) : (GameTree.leaf i).map f = .leaf (f i) :=
  rfl

@[simp] theorem GameTree.map_node (f : ι → α) (ts : List (GameTree ι)) :
    (GameTree.node ts).map f = .node (ts.map (GameTree.map f)) := by
  rw [GameTree.map, GameTree.mapList_eq]

mutual
/-- The leaves of a tree, from left to right. -/
def leafValues : GameTree ι → List ι
  | .leaf i => [i]
  | .node ts => leafValuesList ts

/-- The leaves of a list of trees, from left to right. -/
def leafValuesList : List (GameTree ι) → List ι
  | [] => []
  | t :: ts => leafValues t ++ leafValuesList ts
end

theorem countP_leafValuesList (P : ι → Bool) :
    ∀ ts : List (GameTree ι),
      (leafValuesList ts).countP P = (ts.map fun t => (leafValues t).countP P).sum
  | [] => rfl
  | t :: ts => by
      rw [leafValuesList, List.countP_append, countP_leafValuesList P ts, List.map_cons,
        List.sum_cons]

theorem countP_leafValues_node (P : ι → Bool) (ts : List (GameTree ι)) :
    (leafValues (.node ts)).countP P = (ts.map fun t => (leafValues t).countP P).sum := by
  rw [leafValues, countP_leafValuesList]

/-- Instantiating the variables of a uniform shape gives a uniform tree. -/
theorem Uniform.map {k d : ℕ} {s : GameTree ι} (f : ι → α) (h : Uniform k d s) :
    Uniform k d (s.map f) := by
  induction h with
  | leaf i => exact .leaf (f i)
  | node hlen _ ih =>
      rw [GameTree.map_node]
      refine .node (by rw [List.length_map, hlen]) fun u hu => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
      exact ih t ht

/-! ## Sums over the children -/

private theorem le_sum_map {β : Type*} (c : β → ℕ) :
    ∀ {ts : List β} {u : β}, u ∈ ts → c u ≤ (ts.map c).sum
  | t :: ts, u, h => by
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_add_right _ _
      · exact (le_sum_map c h).trans (Nat.le_add_left _ _)

private theorem length_mul_le_sum_map {β : Type*} (c : β → ℕ) (B : ℕ) :
    ∀ {ts : List β}, (∀ u ∈ ts, B ≤ c u) → ts.length * B ≤ (ts.map c).sum
  | [], _ => by simp
  | t :: ts, h => by
      have h1 := h t List.mem_cons_self
      have h2 := length_mul_le_sum_map c B (ts := ts) fun u hu => h u (List.mem_cons_of_mem t hu)
      rw [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
      omega

/-- One child contributes `A`, every child at least `B`. -/
private theorem add_length_mul_le_sum_map {β : Type*} (c : β → ℕ) (A B : ℕ) :
    ∀ {ts : List β} {u₀ : β}, u₀ ∈ ts → A ≤ c u₀ → (∀ u ∈ ts, B ≤ c u) →
      A + ts.length * B ≤ (ts.map c).sum + B
  | t :: ts, u₀, hmem, hA, hB => by
      have hB' : ∀ u ∈ ts, B ≤ c u := fun u hu => hB u (List.mem_cons_of_mem t hu)
      rw [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
      rcases List.mem_cons.1 hmem with rfl | hmem
      · have := length_mul_le_sum_map c B hB'
        omega
      · have := add_length_mul_le_sum_map c A B hmem hA hB'
        have := hB t List.mem_cons_self
        omega

/-- A list without repeated elements has at most `Q.card` elements in `Q`. -/
theorem countP_mem_le_card [DecidableEq ι] {l : List ι} (hl : l.Nodup) (Q : Finset ι) :
    l.countP (· ∈ Q) ≤ Q.card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  refine Finset.card_le_card fun i hi => ?_
  simpa using (List.mem_filter.1 (List.mem_toFinset.1 hi)).2

/-! ## Minimax values of instantiated shapes -/

section Minimax

variable [LinearOrder α] [BoundedOrder α]

@[simp] theorem minimax_map_leaf (p : Bool) (f : ι → α) (i : ι) :
    minimax p ((GameTree.leaf i).map f) = f i := rfl

@[simp] theorem minimax_map_node (p : Bool) (f : ι → α) (ts : List (GameTree ι)) :
    minimax p ((GameTree.node ts).map f) = minimaxList p (ts.map (GameTree.map f)) := by
  rw [GameTree.map_node, minimax]

mutual
/-- The minimax value is monotone in the leaf values. -/
theorem minimax_map_mono {g h : ι → α} (hgh : ∀ i, g i ≤ h i) :
    ∀ (p : Bool) (s : GameTree ι), minimax p (s.map g) ≤ minimax p (s.map h)
  | _, .leaf i => hgh i
  | p, .node ts => by
      rw [minimax_map_node, minimax_map_node]
      exact minimaxList_map_mono hgh p ts

/-- The best child value is monotone in the leaf values. -/
theorem minimaxList_map_mono {g h : ι → α} (hgh : ∀ i, g i ≤ h i) :
    ∀ (p : Bool) (ts : List (GameTree ι)),
      minimaxList p (ts.map (GameTree.map g)) ≤ minimaxList p (ts.map (GameTree.map h))
  | true, [] => le_rfl
  | false, [] => le_rfl
  | true, t :: ts => by
      simp only [List.map_cons, minimaxList]
      exact max_le_max (minimax_map_mono hgh false t) (minimaxList_map_mono hgh true ts)
  | false, t :: ts => by
      simp only [List.map_cons, minimaxList]
      exact min_le_min (minimax_map_mono hgh true t) (minimaxList_map_mono hgh false ts)
end

/-- A maximizer's value above `⊥` is attained by a child. -/
theorem exists_mem_minimax_false_eq {ts : List (GameTree α)} (h : ⊥ < minimaxList true ts) :
    ∃ u ∈ ts, minimax false u = minimaxList true ts := by
  induction ts with
  | nil => exact absurd h (lt_irrefl _)
  | cons t ts ih =>
      simp only [minimaxList] at h ⊢
      rcases le_total (minimaxList true ts) (minimax false t) with hle | hle
      · exact ⟨t, List.mem_cons_self, (max_eq_left hle).symm⟩
      · rw [max_eq_right hle] at h ⊢
        obtain ⟨u, hu, he⟩ := ih h
        exact ⟨u, List.mem_cons_of_mem t hu, he⟩

/-- A minimizer's value below `⊤` is attained by a child. -/
theorem exists_mem_minimax_true_eq {ts : List (GameTree α)} (h : minimaxList false ts < ⊤) :
    ∃ u ∈ ts, minimax true u = minimaxList false ts := by
  induction ts with
  | nil => exact absurd h (lt_irrefl _)
  | cons t ts ih =>
      simp only [minimaxList] at h ⊢
      rcases le_total (minimax true t) (minimaxList false ts) with hle | hle
      · exact ⟨t, List.mem_cons_self, (min_eq_left hle).symm⟩
      · rw [min_eq_right hle] at h ⊢
        obtain ⟨u, hu, he⟩ := ih h
        exact ⟨u, List.mem_cons_of_mem t hu, he⟩

/-- Each child's value is at most the maximizer's value. -/
theorem minimax_false_le_minimaxList_true {ts : List (GameTree α)} {u : GameTree α}
    (hu : u ∈ ts) : minimax false u ≤ minimaxList true ts :=
  minimaxList_true_le_iff.1 le_rfl u hu

/-- Each child's value is at least the minimizer's value. -/
theorem minimaxList_false_le_minimax_true {ts : List (GameTree α)} {u : GameTree α}
    (hu : u ∈ ts) : minimaxList false ts ≤ minimax true u :=
  le_minimaxList_false_iff.1 le_rfl u hu

/-! ## Strategies inside a determining set -/

section Strategies

variable [DecidableEq ι] {Q : Finset ι}

/-- **The maximizer's strategy.** If the leaves outside `Q` are worth `⊥` under `lo` and the value
of a uniform shape is still above `⊥`, then `Q` holds at least `k ^ ⌊d / 2⌋` of its leaves when the
maximizer moves at the root and `k ^ ⌈d / 2⌉` when the minimizer does. -/
theorem cutLeaves_le_of_bot_lt {lo : ι → α} (hlo : ∀ i ∉ Q, lo i = ⊥) (k : ℕ) :
    ∀ (d : ℕ) (s : GameTree ι), Uniform k d s →
      (⊥ < minimax true (s.map lo) → cutLeaves k d ≤ (leafValues s).countP (· ∈ Q)) ∧
      (⊥ < minimax false (s.map lo) → allLeaves k d ≤ (leafValues s).countP (· ∈ Q))
  | 0, _, hu => by
      cases hu with
      | leaf i =>
        have key : ⊥ < lo i → 1 ≤ (leafValues (.leaf i : GameTree ι)).countP (· ∈ Q) := by
          intro h
          have hi : i ∈ Q := by
            by_contra hi
            rw [hlo i hi] at h
            exact lt_irrefl _ h
          simp [leafValues, hi]
        simp only [minimax_map_leaf, cutLeaves_zero, allLeaves_zero]
        exact ⟨key, key⟩
  | d + 1, _, hu => by
      cases hu with
      | node hlen hts =>
      rename_i ts
      have ih := fun u (hu : u ∈ ts) => cutLeaves_le_of_bot_lt hlo k d u (hts u hu)
      rw [countP_leafValues_node, minimax_map_node, minimax_map_node]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · -- the maximizer moves: some child keeps a value above `⊥`
        obtain ⟨u', hu', he⟩ := exists_mem_minimax_false_eq h
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
        rw [cutLeaves_succ]
        exact ((ih u hu).2 (he ▸ h)).trans
          (le_sum_map (fun t => (leafValues t).countP (· ∈ Q)) hu)
      · -- the minimizer moves: every child keeps a value above `⊥`
        have hall : ∀ u ∈ ts, cutLeaves k d ≤ (leafValues u).countP (· ∈ Q) := fun u hu =>
          (ih u hu).1 (h.trans_le (minimaxList_false_le_minimax_true (List.mem_map_of_mem hu)))
        have hsum := length_mul_le_sum_map (fun t => (leafValues t).countP (· ∈ Q)) _ hall
        rw [hlen] at hsum
        rwa [allLeaves_succ]

/-- **The minimizer's strategy.** If the leaves outside `Q` are worth `⊤` under `hi` and the value
of a uniform shape is still below `⊤`, then `Q` holds at least `k ^ ⌊d / 2⌋` of its leaves when the
minimizer moves at the root and `k ^ ⌈d / 2⌉` when the maximizer does. -/
theorem cutLeaves_le_of_lt_top {hi : ι → α} (hhi : ∀ i ∉ Q, hi i = ⊤) (k : ℕ) :
    ∀ (d : ℕ) (s : GameTree ι), Uniform k d s →
      (minimax false (s.map hi) < ⊤ → cutLeaves k d ≤ (leafValues s).countP (· ∈ Q)) ∧
      (minimax true (s.map hi) < ⊤ → allLeaves k d ≤ (leafValues s).countP (· ∈ Q))
  | 0, _, hu => by
      cases hu with
      | leaf i =>
        have key : hi i < ⊤ → 1 ≤ (leafValues (.leaf i : GameTree ι)).countP (· ∈ Q) := by
          intro h
          have hiQ : i ∈ Q := by
            by_contra hiQ
            rw [hhi i hiQ] at h
            exact lt_irrefl _ h
          simp [leafValues, hiQ]
        simp only [minimax_map_leaf, cutLeaves_zero, allLeaves_zero]
        exact ⟨key, key⟩
  | d + 1, _, hu => by
      cases hu with
      | node hlen hts =>
      rename_i ts
      have ih := fun u (hu : u ∈ ts) => cutLeaves_le_of_lt_top hhi k d u (hts u hu)
      rw [countP_leafValues_node, minimax_map_node, minimax_map_node]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · -- the minimizer moves: some child keeps a value below `⊤`
        obtain ⟨u', hu', he⟩ := exists_mem_minimax_true_eq h
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
        rw [cutLeaves_succ]
        exact ((ih u hu).2 (he ▸ h)).trans
          (le_sum_map (fun t => (leafValues t).countP (· ∈ Q)) hu)
      · -- the maximizer moves: every child keeps a value below `⊤`
        have hall : ∀ u ∈ ts, cutLeaves k d ≤ (leafValues u).countP (· ∈ Q) := fun u hu =>
          (ih u hu).1 ((minimax_false_le_minimaxList_true (List.mem_map_of_mem hu)).trans_lt h)
        have hsum := length_mul_le_sum_map (fun t => (leafValues t).countP (· ∈ Q)) _ hall
        rw [hlen] at hsum
        rwa [allLeaves_succ]

/-- **Principal nodes.** If `lo ≤ hi`, the leaves outside `Q` are worth `⊥` under `lo` and `⊤`
under `hi`, and a uniform shape has the same value `v` under both, strictly between `⊥` and `⊤`,
then `Q` holds at least `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` of its leaves. -/
theorem pvLeaves_le_countP {lo hi : ι → α} (hlo : ∀ i ∉ Q, lo i = ⊥) (hhi : ∀ i ∉ Q, hi i = ⊤)
    (hle : ∀ i, lo i ≤ hi i) (k : ℕ) :
    ∀ (d : ℕ) (p : Bool) (s : GameTree ι) (v : α), Uniform k d s →
      minimax p (s.map lo) = v → minimax p (s.map hi) = v → ⊥ < v → v < ⊤ →
      pvLeaves k d ≤ (leafValues s).countP (· ∈ Q)
  | 0, _, _, v, hu, hl, _, hb, _ => by
      cases hu with
      | leaf i =>
        rw [minimax_map_leaf] at hl
        have hi : i ∈ Q := by
          by_contra hi
          rw [hlo i hi] at hl
          rw [← hl] at hb
          exact lt_irrefl _ hb
        simp [leafValues, hi, pvLeaves_zero]
  | d + 1, p, _, v, hu, hl, hh, hb, ht => by
      cases hu with
      | node hlen hts =>
      rename_i ts
      rw [countP_leafValues_node]
      rw [minimax_map_node] at hl hh
      -- a child `u₀` attains `v` under both inputs; every other child fails the window
      obtain ⟨u₀, hu₀, h₀, hrest⟩ : ∃ u₀ ∈ ts,
          pvLeaves k d ≤ (leafValues u₀).countP (· ∈ Q) ∧
          ∀ u ∈ ts, cutLeaves k d ≤ (leafValues u).countP (· ∈ Q) := by
        cases p with
        | true =>
          obtain ⟨u', hu', he⟩ := exists_mem_minimax_false_eq (hl ▸ hb)
          obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 hu'
          rw [hl] at he
          have hup : minimax false (u₀.map hi) ≤ v :=
            hh ▸ minimax_false_le_minimaxList_true (List.mem_map_of_mem hu₀)
          have hdown : v ≤ minimax false (u₀.map hi) := he ▸ minimax_map_mono hle false u₀
          refine ⟨u₀, hu₀, pvLeaves_le_countP hlo hhi hle k d false u₀ v (hts u₀ hu₀) he
            (le_antisymm hup hdown) hb ht, fun u hu => ?_⟩
          have hu' : minimax false (u.map hi) ≤ v :=
            hh ▸ minimax_false_le_minimaxList_true (List.mem_map_of_mem hu)
          exact (cutLeaves_le_of_lt_top hhi k d u (hts u hu)).1 (hu'.trans_lt ht)
        | false =>
          obtain ⟨u', hu', he⟩ := exists_mem_minimax_true_eq (hh ▸ ht)
          obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 hu'
          rw [hh] at he
          have hdown : v ≤ minimax true (u₀.map lo) :=
            hl ▸ minimaxList_false_le_minimax_true (List.mem_map_of_mem hu₀)
          have hup : minimax true (u₀.map lo) ≤ v := he ▸ minimax_map_mono hle true u₀
          refine ⟨u₀, hu₀, pvLeaves_le_countP hlo hhi hle k d true u₀ v (hts u₀ hu₀)
            (le_antisymm hup hdown) he hb ht, fun u hu => ?_⟩
          have hu' : v ≤ minimax true (u.map lo) :=
            hl ▸ minimaxList_false_le_minimax_true (List.mem_map_of_mem hu)
          exact (cutLeaves_le_of_bot_lt hlo k d u (hts u hu)).1 (hb.trans_le hu')
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 :=
        ⟨ts.length - 1, by have := List.length_pos_of_mem hu₀; omega⟩
      have hsum := add_length_mul_le_sum_map _ _ _ hu₀ h₀ hrest
      rw [hlen, Nat.succ_mul] at hsum
      rw [pvLeaves_succ_succ]
      omega

end Strategies

/-! ## The lower bound -/

/-- **Knuth and Moore's lower bound, certificate form.** On a uniform shape of branching factor `k`
and depth `d` with distinct leaf variables, a set `Q` of leaves whose values determine the minimax
value at `f` has at least `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` elements, if that value lies strictly
between `⊥` and `⊤`. -/
theorem minimax_certificate_lower {k d : ℕ} {p : Bool} {s : GameTree ι} (hu : Uniform k d s)
    (hs : (leafValues s).Nodup) {f : ι → α} (Q : Finset ι)
    (hQ : ∀ g : ι → α, (∀ i ∈ Q, g i = f i) → minimax p (s.map g) = minimax p (s.map f))
    (hbot : ⊥ < minimax p (s.map f)) (htop : minimax p (s.map f) < ⊤) :
    k ^ ((d + 1) / 2) + k ^ (d / 2) - 1 ≤ Q.card := by
  classical
  have hc := pvLeaves_le_countP (Q := Q) (lo := fun i => if i ∈ Q then f i else ⊥)
    (hi := fun i => if i ∈ Q then f i else ⊤) (fun i h => by simp [h]) (fun i h => by simp [h])
    (fun i => by split_ifs <;> simp) k d p s _ hu (hQ _ fun i h => by simp [h])
    (hQ _ fun i h => by simp [h]) hbot htop
  exact hc.trans (countP_mem_le_card hs Q)

/-- **Knuth and Moore's lower bound.** Every query algorithm that computes the minimax value of a
uniform shape of branching factor `k` and depth `d` with distinct leaf variables reads at least
`k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` distinct leaves on every input whose value lies strictly between
`⊥` and `⊤`. -/
theorem minimax_queries_lower [DecidableEq ι] {k d : ℕ} {p : Bool} {s : GameTree ι}
    (hu : Uniform k d s) (hs : (leafValues s).Nodup) (T : OracleComp ι α α)
    (hT : ∀ g : ι → α, T.run g = minimax p (s.map g)) {f : ι → α}
    (hbot : ⊥ < minimax p (s.map f)) (htop : minimax p (s.map f) < ⊤) :
    k ^ ((d + 1) / 2) + k ^ (d / 2) - 1 ≤ (T.queries f).toFinset.card :=
  minimax_certificate_lower hu hs _ (fun g hg => by
    rw [← hT, ← hT]
    exact (OracleComp.run_congr T fun i hi => (hg i (List.mem_toFinset.2 hi)).symm).1.symm)
    hbot htop

/-- The total number of queries obeys the same bound. -/
theorem minimax_queries_length_lower {k d : ℕ} {p : Bool} {s : GameTree ι} (hu : Uniform k d s)
    (hs : (leafValues s).Nodup) (T : OracleComp ι α α)
    (hT : ∀ g : ι → α, T.run g = minimax p (s.map g)) {f : ι → α}
    (hbot : ⊥ < minimax p (s.map f)) (htop : minimax p (s.map f) < ⊤) :
    k ^ ((d + 1) / 2) + k ^ (d / 2) - 1 ≤ (T.queries f).length := by
  classical
  exact (minimax_queries_lower hu hs T hT hbot htop).trans (List.toFinset_card_le _)

end Minimax

/-! ## Alpha-beta as a query algorithm -/

section AlphaBetaQuery

variable [LinearOrder α]

@[simp] private theorem run_pure' {X : Type*} {Y β : Type v} (O : X → Y) (b : β) :
    (pure b : OracleComp X Y β).run O = b := rfl

@[simp] private theorem queries_pure' {X : Type*} {Y β : Type v} (O : X → Y) (b : β) :
    (pure b : OracleComp X Y β).queries O = [] := rfl

private theorem run_bind' {X : Type*} {Y β γ : Type v} (O : X → Y) (c : OracleComp X Y β)
    (g : β → OracleComp X Y γ) : (c >>= g).run O = (g (c.run O)).run O :=
  OracleComp.run_bind O g c

private theorem queries_bind {X : Type*} {Y β γ : Type v} (O : X → Y) :
    ∀ (c : OracleComp X Y β) (g : β → OracleComp X Y γ),
      (c >>= g).queries O = c.queries O ++ (g (c.run O)).queries O
  | .pure _, _ => rfl
  | .liftBind x k, g => by
      change x :: OracleComp.queries O (k (O x) >>= g) =
        x :: (OracleComp.queries O (k (O x)) ++ _)
      rw [queries_bind O (k (O x)) g]
      rfl

mutual
/-- `alphaBeta` as a query algorithm: it queries a leaf where `alphaBeta` evaluates it. -/
def alphaBetaQuery : Bool → α → α → GameTree ι → OracleComp ι α α
  | _, _, _, .leaf i => OracleComp.query i OracleComp.done
  | p, a, b, .node ts => alphaBetaQueryList p a b ts

/-- The scan over the children, as in `alphaBetaList`. -/
def alphaBetaQueryList : Bool → α → α → List (GameTree ι) → OracleComp ι α α
  | true, a, _, [] => pure a
  | false, _, b, [] => pure b
  | true, a, b, t :: ts => do
      let v ← alphaBetaQuery false a b t
      let a' := max a v
      if b ≤ a' then pure a' else alphaBetaQueryList true a' b ts
  | false, a, b, t :: ts => do
      let v ← alphaBetaQuery true a b t
      let b' := min b v
      if b' ≤ a then pure b' else alphaBetaQueryList false a b' ts
end

mutual
/-- The query algorithm computes what `alphaBeta` computes on the instantiated tree, and makes one
query per leaf `alphaBeta` evaluates. -/
theorem alphaBetaQuery_spec (f : ι → α) : ∀ (p : Bool) (a b : α) (s : GameTree ι),
    (alphaBetaQuery p a b s).run f = (alphaBeta p a b (s.map f)).ret ∧
    ((alphaBetaQuery p a b s).queries f).length = (alphaBeta p a b (s.map f)).time
  | _, _, _, .leaf _ => ⟨rfl, rfl⟩
  | p, a, b, .node ts => by
      rw [alphaBetaQuery, GameTree.map, GameTree.mapList_eq, alphaBeta]
      exact alphaBetaQueryList_spec f p a b ts

/-- The scan over the children agrees with `alphaBetaList`. -/
theorem alphaBetaQueryList_spec (f : ι → α) : ∀ (p : Bool) (a b : α) (ts : List (GameTree ι)),
    (alphaBetaQueryList p a b ts).run f = (alphaBetaList p a b (ts.map (GameTree.map f))).ret ∧
    ((alphaBetaQueryList p a b ts).queries f).length =
      (alphaBetaList p a b (ts.map (GameTree.map f))).time
  | true, _, _, [] => by simp [alphaBetaQueryList, alphaBetaList]
  | false, _, _, [] => by simp [alphaBetaQueryList, alphaBetaList]
  | true, a, b, t :: ts => by
      obtain ⟨he, hl⟩ := alphaBetaQuery_spec f false a b t
      simp only [alphaBetaQueryList, alphaBetaList, List.map_cons, run_bind',
        queries_bind, List.length_append, TimeM.ret_bind, TimeM.time_bind, he, hl]
      split_ifs
      · simp
      · obtain ⟨he', hl'⟩ := alphaBetaQueryList_spec f true (max a (alphaBeta false a b
          (t.map f)).ret) b ts
        exact ⟨he', by rw [hl']⟩
  | false, a, b, t :: ts => by
      obtain ⟨he, hl⟩ := alphaBetaQuery_spec f true a b t
      simp only [alphaBetaQueryList, alphaBetaList, List.map_cons, run_bind',
        queries_bind, List.length_append, TimeM.ret_bind, TimeM.time_bind, he, hl]
      split_ifs
      · simp
      · obtain ⟨he', hl'⟩ := alphaBetaQueryList_spec f false a (min b (alphaBeta true a b
          (t.map f)).ret) ts
        exact ⟨he', by rw [hl']⟩
end

theorem run_alphaBetaQuery (f : ι → α) (p : Bool) (a b : α) (s : GameTree ι) :
    (alphaBetaQuery p a b s).run f = (alphaBeta p a b (s.map f)).ret :=
  (alphaBetaQuery_spec f p a b s).1

theorem length_queries_alphaBetaQuery (f : ι → α) (p : Bool) (a b : α) (s : GameTree ι) :
    ((alphaBetaQuery p a b s).queries f).length = (alphaBeta p a b (s.map f)).time :=
  (alphaBetaQuery_spec f p a b s).2

variable [BoundedOrder α]

/-- Alpha-beta with the full window is a correct query algorithm. -/
theorem run_alphaBetaQuery_bot_top (f : ι → α) (p : Bool) (s : GameTree ι) :
    (alphaBetaQuery p ⊥ ⊤ s).run f = minimax p (s.map f) := by
  rw [run_alphaBetaQuery, alphaBeta_bot_top]

/-- **Alpha-beta is optimal on perfectly ordered uniform trees** (Knuth and Moore 1975). On a
uniform shape with distinct leaf variables, if the input `f` makes the tree perfectly ordered with
a value strictly between `⊥` and `⊤`, alpha-beta with the full window makes no more queries on `f`
than any correct query algorithm reads distinct leaves on `f`. -/
theorem alphaBetaQuery_optimal [DecidableEq ι] {k d : ℕ} {p : Bool} {s : GameTree ι}
    (hu : Uniform k d s) (hs : (leafValues s).Nodup) {f : ι → α}
    (hpo : PerfectlyOrdered p (s.map f)) (hbot : ⊥ < minimax p (s.map f))
    (htop : minimax p (s.map f) < ⊤) (T : OracleComp ι α α)
    (hT : ∀ g : ι → α, T.run g = minimax p (s.map g)) :
    ((alphaBetaQuery p ⊥ ⊤ s).queries f).length ≤ (T.queries f).toFinset.card := by
  rw [length_queries_alphaBetaQuery, alphaBeta_leafCount_perfect (hu.map f) hpo hbot htop]
  exact minimax_queries_lower hu hs T hT hbot htop

end AlphaBetaQuery

end Cslib.Algorithms.Lean.AlphaBeta
