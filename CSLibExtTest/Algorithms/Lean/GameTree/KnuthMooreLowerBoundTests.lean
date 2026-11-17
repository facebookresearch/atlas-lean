/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.KnuthMooreLowerBound
public meta import CSLibExt.Algorithms.Lean.GameTree.KnuthMooreLowerBound
public import Mathlib.Order.Fin.Basic
public meta import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the Knuth–Moore lower bound

Values lie in `Fin 101` (`⊥ = 0`, `⊤ = 100`); the shape `s22` is the uniform tree with `k = d = 2`
and leaf variables `0, 1, 2, 3`, so the bound is `2 ^ 1 + 2 ^ 1 - 1 = 3`.

* Positive: every correct query algorithm reads at least three leaves on the perfectly ordered
  input `3, 5, 2, 9`, and alpha-beta reads exactly three there (`alphaBetaQuery_optimal`).
* Nonvacuity: alpha-beta is a correct query algorithm, so the correctness hypothesis is met; at
  depth `0` the bound is one leaf.
* Negative: the worst ordering of the same leaves makes alpha-beta read all four.
* Boundary: on an input valued `⊤` (and one valued `⊥`) alpha-beta is still correct but reads only
  two leaves, so the value hypotheses cannot be dropped; on a shape whose leaves repeat one
  variable, a one-query algorithm is correct, so distinct leaf variables cannot be dropped.
* Executed: on pseudo-random uniform shapes (`k = 1 .. 3`, `d = 0 .. 4`), alpha-beta as a query
  algorithm returns the minimax value, queries the leaves `alphaBeta` evaluates, and its queried
  leaves determine the value (all leaves outside them set to `⊥`, or all to `⊤`, give the same
  value), reading at least the bound whenever the value lies strictly between `⊥` and `⊤`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean Cslib.Crypto.Framework

private abbrev V := Fin 101

/-- The uniform shape with `k = d = 2` and leaf variables `0, 1, 2, 3`. -/
private def s22 : GameTree (Fin 4) := .node [.node [.leaf 0, .leaf 1], .node [.leaf 2, .leaf 3]]

private theorem s22_uniform : Uniform 2 2 s22 := by
  refine .node rfl ?_
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;>
  · refine .node rfl ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact .leaf _

private theorem s22_nodup : (leafValues s22).Nodup := by decide

/-- Perfectly ordered: the maximizer's first move is worth `3`, the second `2`. -/
private def best : Fin 4 → V := ![3, 5, 2, 9]

/-- The same leaves in the worst order. -/
private def worst : Fin 4 → V := ![9, 2, 5, 3]

/-- The maximizer's first move is worth `⊤`. -/
private def topIn : Fin 4 → V := ![100, 100, 7, 8]

/-- Both of the maximizer's moves are worth `⊥`. -/
private def botIn : Fin 4 → V := ![0, 50, 0, 60]

private theorem best_ordered : PerfectlyOrdered true (s22.map best) := by
  show PerfectlyOrdered true (.node [.node [.leaf 3, .leaf 5], .node [.leaf 2, .leaf 9]])
  refine .node (by decide) ?_
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;>
  · refine .node (by decide) ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact .leaf _ _

/-! ## Positive checks -/

/-- Every correct query algorithm reads at least three leaves on the input `3, 5, 2, 9`. -/
example (T : OracleComp (Fin 4) V V) (hT : ∀ g, T.run g = minimax true (s22.map g)) :
    3 ≤ (T.queries best).toFinset.card :=
  minimax_queries_lower s22_uniform s22_nodup T hT (by decide) (by decide)

/-- The bound also holds on the worst ordering, where alpha-beta reads all four leaves. -/
example (T : OracleComp (Fin 4) V V) (hT : ∀ g, T.run g = minimax true (s22.map g)) :
    3 ≤ (T.queries worst).toFinset.card :=
  minimax_queries_lower s22_uniform s22_nodup T hT (by decide) (by decide)

/-- Alpha-beta reads exactly the three leaves `0, 1, 2` there, the fewest possible. -/
example : (alphaBetaQuery true (⊥ : V) ⊤ s22).queries best = [0, 1, 2] := by decide

example (T : OracleComp (Fin 4) V V) (hT : ∀ g, T.run g = minimax true (s22.map g)) :
    ((alphaBetaQuery true (⊥ : V) ⊤ s22).queries best).length ≤ (T.queries best).toFinset.card :=
  alphaBetaQuery_optimal s22_uniform s22_nodup best_ordered (by decide) (by decide) T hT

/-! ## Nonvacuity -/

/-- Alpha-beta with the full window satisfies the correctness hypothesis. -/
example : ∀ g, (alphaBetaQuery true (⊥ : V) ⊤ s22).run g = minimax true (s22.map g) :=
  fun g => run_alphaBetaQuery_bot_top g true s22

example : 3 ≤ ((alphaBetaQuery true (⊥ : V) ⊤ s22).queries best).toFinset.card :=
  minimax_queries_lower s22_uniform s22_nodup _ (fun g => run_alphaBetaQuery_bot_top g true s22)
    (by decide) (by decide)

/-- Depth `0`: one leaf, for every branching factor. -/
example (k : ℕ) (T : OracleComp Unit V V)
    (hT : ∀ g, T.run g = minimax false ((GameTree.leaf () : GameTree Unit).map g))
    (f : Unit → V) (h0 : ⊥ < f ()) (h1 : f () < ⊤) : 1 ≤ (T.queries f).toFinset.card := by
  have := minimax_queries_lower (k := k) (.leaf ()) (by simp [leafValues]) T hT (f := f)
    (by rw [minimax_map_leaf]; exact h0) (by rw [minimax_map_leaf]; exact h1)
  simpa using this

/-! ## Negative and boundary checks -/

/-- Worst ordering: alpha-beta reads all `b ^ d = 4` leaves. -/
example : (alphaBetaQuery true (⊥ : V) ⊤ s22).queries worst = [0, 1, 2, 3] := by decide

/-- Value `⊤`: alpha-beta is correct but reads two leaves, below the bound. -/
example : minimax true (s22.map topIn) = ⊤ := by decide

example : (alphaBetaQuery true (⊥ : V) ⊤ s22).queries topIn = [0, 1] := by decide

/-- Value `⊥`: alpha-beta is correct but reads two leaves, below the bound. -/
example : minimax true (s22.map botIn) = ⊥ := by decide

example : (alphaBetaQuery true (⊥ : V) ⊤ s22).queries botIn = [0, 2] := by decide

/-- A shape whose four leaves all carry variable `0`. -/
private def same22 : GameTree (Fin 4) :=
  .node [.node [.leaf 0, .leaf 0], .node [.leaf 0, .leaf 0]]

example : ¬ (leafValues same22).Nodup := by decide

/-- The algorithm that reads leaf `0` and outputs its value. -/
private def readZero : OracleComp (Fin 4) V V := OracleComp.query 0 OracleComp.done

/-- On `same22` a one-query algorithm is correct, so distinct leaf variables are needed. -/
example : ∀ g : Fin 4 → V, readZero.run g = minimax true (same22.map g) := by
  intro g
  change g 0 = _
  simp [same22, minimax, minimaxList]

example : (readZero.queries best).toFinset.card = 1 := by decide

/-! ## Executed checks on pseudo-random shapes -/

private meta def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- The uniform shape with branching `k` and depth `d`, leaves numbered from `n` left to right. -/
private meta def shape (k : ℕ) : ℕ → ℕ → ℕ × GameTree ℕ
  | 0, n => (n + 1, .leaf n)
  | d + 1, n =>
    let (n, ts) := (List.range k).foldl (fun (acc : ℕ × List (GameTree ℕ)) _ =>
      let (n', t) := shape k d acc.1
      (n', acc.2 ++ [t])) (n, [])
    (n, .node ts)

#eval do
  let mut runs := 0
  let mut principal := 0
  for k in [1, 2, 3] do
    for d in [0, 1, 2, 3, 4] do
      let (n, s) := shape k d 0
      for i in [0:16] do
        -- even runs draw values from 1 .. 99, odd runs from 0 .. 4 (ties and `⊥` leaves)
        let vals : Array V := (List.range n).foldl (fun (acc : ℕ × Array V) _ =>
          let x := lcg acc.1
          (x, acc.2.push (Fin.ofNat 101 (if i % 2 == 0 then 1 + x / 7 % 99 else x / 7 % 5))))
          (i * 7919 + 31 * k + d + 1, #[]) |>.2
        let f : ℕ → V := fun j => vals.getD j 0
        let p := i % 4 < 2
        let A := alphaBetaQuery p ⊥ ⊤ s
        let qs := A.queries f
        let r := alphaBeta p ⊥ ⊤ (s.map f)
        let v := minimax p (s.map f)
        unless A.run f == v && qs.length == r.time do
          throw (IO.userError s!"k={k} d={d} run {i}: query run disagrees with alphaBeta")
        let lo : ℕ → V := fun j => if qs.contains j then f j else ⊥
        let hi : ℕ → V := fun j => if qs.contains j then f j else ⊤
        unless minimax p (s.map lo) == v && minimax p (s.map hi) == v do
          throw (IO.userError s!"k={k} d={d} run {i}: queried leaves do not determine the value")
        if ⊥ < v && v < ⊤ then
          let want := k ^ ((d + 1) / 2) + k ^ (d / 2) - 1
          unless want ≤ qs.eraseDups.length do
            throw (IO.userError s!"k={k} d={d} run {i}: {qs.eraseDups.length} < {want}")
          principal := principal + 1
        runs := runs + 1
  IO.println s!"{runs} alpha-beta query runs (k = 1..3, d = 0..4) agree with alphaBeta and \
    read a determining set; {principal} of them have a value strictly inside and read at least \
    k ^ ⌈d/2⌉ + k ^ ⌊d/2⌋ - 1 leaves"

/-! ## Axioms -/

#print axioms minimax_certificate_lower
#print axioms minimax_queries_lower
#print axioms minimax_queries_length_lower
#print axioms alphaBetaQuery_optimal
#print axioms alphaBetaQuery_spec

end Cslib.Algorithms.Lean.AlphaBeta
