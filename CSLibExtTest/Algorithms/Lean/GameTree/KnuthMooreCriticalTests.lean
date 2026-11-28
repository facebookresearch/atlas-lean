/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.KnuthMooreCritical
public import Mathlib.Order.Fin.Basic

/-!
# Tests for Knuth and Moore's Theorem 1 (critical positions)

Values lie in `Fin 101` (`⊥ = 0`, `⊤ = 100`). The checks run `alphaBetaVisits` with `decide`:

* a perfectly ordered uniform tree of degree 3 and height 4 (the leaves of Knuth and Moore's
  Fig. 1, reordered): 37 examined positions, none twice, exactly the critical positions, and its
  17 examined leaves are the 17 critical leaves;
* Knuth and Moore's Fig. 1 itself, which is not perfectly ordered: 55 examined positions and 31
  examined leaves, not all of them critical;
* height `0`, through `alphaBetaVisits_eq_critical`;
* a perfectly ordered tree of degree 3 and height 3 with many tied values, where cutoffs fire on
  ties;
* a maximizer root valued `⊤`: alpha-beta cuts off after the first move at the root, and the
  examined positions are those with the move `0` at every even index, which leaves out critical
  positions.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

private abbrev V := Fin 101

/-- Proves `Uniform k d t` or `PerfectlyOrdered p t` for a concrete ternary tree `t`. -/
syntax "ternary_tree" : tactic

macro_rules
  | `(tactic| ternary_tree) => `(tactic|
      first
      | exact .leaf _
      | exact .leaf _ _
      | refine .node ?_ ?_
        · decide
        · intro u hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with h | h | h <;> subst h <;> ternary_tree)

/-- The critical positions with at most `d` moves, each below `k`. -/
private def criticalUpTo (k d : ℕ) : List (List ℕ) :=
  ((List.range (d + 1)).flatMap (deweyPaths k)).filter (fun a => decide (Critical a))

/-! ## A perfectly ordered tree of degree 3 and height 4 -/

/-- Knuth and Moore's Fig. 1 (1975, §3): the uniform tree of degree 3 and height 4 whose 81 leaves
carry the first 81 decimal digits of `π`; its value is `2`. -/
private def piTree : GameTree V :=
  .node [
    .node [
      .node [.node [.leaf 3, .leaf 1, .leaf 4], .node [.leaf 1, .leaf 5, .leaf 9],
        .node [.leaf 2, .leaf 6, .leaf 5]],
      .node [.node [.leaf 3, .leaf 5, .leaf 8], .node [.leaf 9, .leaf 7, .leaf 9],
        .node [.leaf 3, .leaf 2, .leaf 3]],
      .node [.node [.leaf 8, .leaf 4, .leaf 6], .node [.leaf 2, .leaf 6, .leaf 4],
        .node [.leaf 3, .leaf 3, .leaf 8]]],
    .node [
      .node [.node [.leaf 3, .leaf 2, .leaf 7], .node [.leaf 9, .leaf 5, .leaf 0],
        .node [.leaf 2, .leaf 8, .leaf 8]],
      .node [.node [.leaf 4, .leaf 1, .leaf 9], .node [.leaf 7, .leaf 1, .leaf 6],
        .node [.leaf 9, .leaf 3, .leaf 9]],
      .node [.node [.leaf 9, .leaf 3, .leaf 7], .node [.leaf 5, .leaf 1, .leaf 0],
        .node [.leaf 5, .leaf 8, .leaf 2]]],
    .node [
      .node [.node [.leaf 0, .leaf 9, .leaf 7], .node [.leaf 4, .leaf 9, .leaf 4],
        .node [.leaf 4, .leaf 5, .leaf 9]],
      .node [.node [.leaf 2, .leaf 3, .leaf 0], .node [.leaf 7, .leaf 8, .leaf 1],
        .node [.leaf 6, .leaf 4, .leaf 0]],
      .node [.node [.leaf 6, .leaf 2, .leaf 8], .node [.leaf 6, .leaf 2, .leaf 0],
        .node [.leaf 8, .leaf 9, .leaf 9]]]]

/-- The tree of `piTree` with the successors of every position reordered so that a best move
comes first: a perfectly ordered uniform tree of degree 3 and height 4, of value `2`. -/
private def piPerfect : GameTree V :=
  .node [
    .node [
      .node [.node [.leaf 2, .leaf 6, .leaf 5], .node [.leaf 1, .leaf 3, .leaf 4],
        .node [.leaf 1, .leaf 5, .leaf 9]],
      .node [.node [.leaf 7, .leaf 9, .leaf 9], .node [.leaf 3, .leaf 5, .leaf 8],
        .node [.leaf 2, .leaf 3, .leaf 3]],
      .node [.node [.leaf 4, .leaf 8, .leaf 6], .node [.leaf 2, .leaf 6, .leaf 4],
        .node [.leaf 3, .leaf 3, .leaf 8]]],
    .node [
      .node [.node [.leaf 2, .leaf 3, .leaf 7], .node [.leaf 0, .leaf 9, .leaf 5],
        .node [.leaf 2, .leaf 8, .leaf 8]],
      .node [.node [.leaf 3, .leaf 9, .leaf 9], .node [.leaf 1, .leaf 4, .leaf 9],
        .node [.leaf 1, .leaf 7, .leaf 6]],
      .node [.node [.leaf 3, .leaf 9, .leaf 7], .node [.leaf 0, .leaf 5, .leaf 1],
        .node [.leaf 2, .leaf 5, .leaf 8]]],
    .node [
      .node [.node [.leaf 1, .leaf 7, .leaf 8], .node [.leaf 0, .leaf 2, .leaf 3],
        .node [.leaf 0, .leaf 6, .leaf 4]],
      .node [.node [.leaf 4, .leaf 9, .leaf 4], .node [.leaf 0, .leaf 9, .leaf 7],
        .node [.leaf 4, .leaf 5, .leaf 9]],
      .node [.node [.leaf 8, .leaf 9, .leaf 9], .node [.leaf 2, .leaf 6, .leaf 8],
        .node [.leaf 0, .leaf 6, .leaf 2]]]]

private theorem piPerfect_uniform : Uniform 3 4 piPerfect := by ternary_tree

private theorem piPerfect_ordered : PerfectlyOrdered true piPerfect := by ternary_tree

example : minimax true piPerfect = 2 := by decide

/-- Theorem 1 applies to `piPerfect`: its hypotheses hold. -/
example : (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2.Nodup ∧
    ∀ a : List ℕ, a ∈ (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2 ↔
      a.length ≤ 4 ∧ (∀ x ∈ a, x < 3) ∧ Critical a :=
  alphaBetaVisits_eq_critical piPerfect_uniform piPerfect_ordered (by decide) (by decide)

/-- Its conclusion, computed: 37 positions, none twice, all critical, and every critical
position. -/
example : (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2.length = 37 := by decide

example : (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2.Nodup := by decide

example : ∀ a ∈ (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2,
    a.length ≤ 4 ∧ (∀ x ∈ a, x < 3) ∧ Critical a := by decide

example : ∀ a ∈ criticalUpTo 3 4, a ∈ (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2 := by decide

/-- The 17 examined leaves are the 17 critical leaves, in lexicographic order, and they are the
leaves `alphaBeta` evaluates. -/
example : (alphaBetaVisits true ⊥ ⊤ [] piPerfect).2.filter (fun q => q.length = 4) =
    (deweyPaths 3 4).filter (fun a => decide (Critical a)) := by decide

example : ((deweyPaths 3 4).filter (fun a => decide (Critical a))).length = 17 := by decide

example : (alphaBeta true ⊥ ⊤ piPerfect).time = 17 := by decide

example : (alphaBetaVisits true ⊥ ⊤ [] piPerfect).1 = (alphaBeta true ⊥ ⊤ piPerfect).ret := by
  decide

/-! ## Negative control: Knuth and Moore's Fig. 1 -/

/-- Fig. 1 is not perfectly ordered: at position `[0, 0]` the first move is worth `1` and the
best move `2`. -/
example : ¬ PerfectlyOrdered true piTree := by
  intro h
  cases h with
  | node _ h0 =>
    cases h0 _ List.mem_cons_self with
    | node _ h1 =>
      cases h1 _ List.mem_cons_self with
      | node hfirst _ => exact absurd hfirst (by decide)

example : minimax true piTree = 2 := by decide

example : (alphaBetaVisits true ⊥ ⊤ [] piTree).1 = 2 := by decide

example : (alphaBetaVisits true ⊥ ⊤ [] piTree).2.length = 55 := by decide

example : ((alphaBetaVisits true ⊥ ⊤ [] piTree).2.filter (fun q => q.length = 4)).length = 31 := by
  decide

example : (alphaBeta true ⊥ ⊤ piTree).time = 31 := by decide

/-- Without perfect ordering the conclusion of Theorem 1 fails: some examined position is not
critical. -/
example : ¬ ∀ a ∈ (alphaBetaVisits true ⊥ ⊤ [] piTree).2, Critical a := by decide

/-! ## Height `0` -/

example (x : V) : alphaBetaVisits true ⊥ ⊤ [] (.leaf x) = (x, [[]]) := rfl

/-- Theorem 1 at height `0`, for every branching factor: only the root is examined. -/
example (k : ℕ) : ∀ a : List ℕ, a ∈ (alphaBetaVisits false ⊥ ⊤ [] (.leaf (50 : V))).2 ↔
    a.length ≤ 0 ∧ (∀ x ∈ a, x < k) ∧ Critical a :=
  (alphaBetaVisits_eq_critical (.leaf _) (.leaf _ _) (by decide) (by decide)).2

/-! ## Ties -/

/-- A perfectly ordered uniform tree of degree 3 and height 3 with values `1` and `2` only; at
positions `[0, 2]`, `[1]` and `[2]` the cutoff fires on a tie. -/
private def tieTree : GameTree V :=
  .node [
    .node [.node [.leaf 1, .leaf 1, .leaf 1], .node [.leaf 2, .leaf 1, .leaf 2],
      .node [.leaf 1, .leaf 1, .leaf 1]],
    .node [.node [.leaf 1, .leaf 1, .leaf 1], .node [.leaf 2, .leaf 2, .leaf 2],
      .node [.leaf 1, .leaf 1, .leaf 1]],
    .node [.node [.leaf 1, .leaf 1, .leaf 1], .node [.leaf 1, .leaf 1, .leaf 1],
      .node [.leaf 2, .leaf 2, .leaf 1]]]

private theorem tieTree_uniform : Uniform 3 3 tieTree := by ternary_tree

private theorem tieTree_ordered : PerfectlyOrdered true tieTree := by ternary_tree

example : minimax true tieTree = 1 := by decide

example : (alphaBetaVisits true ⊥ ⊤ [] tieTree).2.length = 20 := by decide

example : (alphaBetaVisits true ⊥ ⊤ [] tieTree).2.Nodup := by decide

example : ∀ a ∈ (alphaBetaVisits true ⊥ ⊤ [] tieTree).2,
    a.length ≤ 3 ∧ (∀ x ∈ a, x < 3) ∧ Critical a := by decide

example : ∀ a ∈ criticalUpTo 3 3, a ∈ (alphaBetaVisits true ⊥ ⊤ [] tieTree).2 := by decide

example : (alphaBeta true ⊥ ⊤ tieTree).time = 11 := by decide

/-! ## Boundary: a maximizer root valued `⊤` -/

/-- A perfectly ordered uniform tree of degree 3 and height 3 whose value for the maximizer is
`⊤`. -/
private def topTree : GameTree V :=
  .node [
    .node [.node [.leaf 100, .leaf 1, .leaf 2], .node [.leaf 100, .leaf 3, .leaf 4],
      .node [.leaf 100, .leaf 5, .leaf 6]],
    .node [.node [.leaf 7, .leaf 1, .leaf 2], .node [.leaf 9, .leaf 8, .leaf 7],
      .node [.leaf 8, .leaf 8, .leaf 8]],
    .node [.node [.leaf 5, .leaf 5, .leaf 1], .node [.leaf 6, .leaf 2, .leaf 3],
      .node [.leaf 5, .leaf 4, .leaf 4]]]

private theorem topTree_uniform : Uniform 3 3 topTree := by ternary_tree

private theorem topTree_ordered : PerfectlyOrdered true topTree := by ternary_tree

example : minimax true topTree = ⊤ := by decide

/-- Alpha-beta examines only the positions with the move `0` at every even index (Knuth and
Moore, p. 306: `3 ^ ⌊3 / 2⌋ = 3` leaves). -/
example : (alphaBetaVisits true ⊥ ⊤ [] topTree).2 =
    [[], [0], [0, 0], [0, 0, 0], [0, 1], [0, 1, 0], [0, 2], [0, 2, 0]] := by decide

/-- So the conclusion of Theorem 1 fails without `minimax p t < ⊤`: the critical position `[1]`
is not examined. -/
example : Critical [1] ∧ [1] ∉ (alphaBetaVisits true ⊥ ⊤ [] topTree).2 := by decide

end Cslib.Algorithms.Lean.AlphaBeta
