/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.KnuthMoore
public meta import CSLibExt.Algorithms.Lean.GameTree.KnuthMoore
public import Mathlib.Order.Fin.Basic
public meta import Mathlib.Order.Fin.Basic

/-!
# Tests for the Knuth–Moore best-case count

Values lie in `Fin 101` (`⊥ = 0`, `⊤ = 100`). Executed fixtures build pseudo-random uniform trees
of branching factor `1` to `4` and depth `0` to `5`, move a best child to the front at every node,
and check that alpha-beta with the full window evaluates exactly
`k ^ ((d + 1) / 2) + k ^ (d / 2) - 1` leaves, including trees with many ties. Closed checks:
the ledger examples `b = 2, d = 2` (three leaves) and `d = 0` (one leaf) through
`alphaBeta_leafCount_perfect`, the worst ordering of the same tree (all four leaves, and not
perfectly ordered), and a root valued `⊤`, where the count drops to two and the theorem's
`minimax p t < ⊤` hypothesis fails.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean

private abbrev V := Fin 101

private meta def lf (x : ℕ) : GameTree V := .leaf (Fin.ofNat 101 x)

private meta def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- A pseudo-random uniform tree: branching `k`, depth `d`, leaf values in `1 .. m`. -/
private meta def uniformTree (k m : ℕ) (s : ℕ) : ℕ → ℕ × GameTree V
  | 0 => let s := lcg s; (s, lf (1 + s / 7 % m))
  | d + 1 =>
    let (s, ts) := (List.range k).foldl (fun (acc : ℕ × List (GameTree V)) _ =>
      let (s', t) := uniformTree k m acc.1 d
      (s', acc.2 ++ [t])) (s, [])
    (s, .node ts)

/-- Order every node so that its first child attains the node's value for the player to move. -/
private meta partial def perfect (p : Bool) : GameTree V → GameTree V
  | .leaf x => .leaf x
  | .node ts =>
    let ts := ts.map (perfect (!p))
    let m := minimaxList p ts
    match ts.findIdx? (fun u => minimax (!p) u == m) with
    | some i => match ts[i]? with
      | some u => .node (u :: ts.eraseIdx i)
      | none => .node ts
    | none => .node ts

/-- Executable check of `PerfectlyOrdered`. -/
private meta partial def isPerfect (p : Bool) : GameTree V → Bool
  | .leaf _ => true
  | .node [] => false
  | .node (t :: ts) =>
    minimax p (.node (t :: ts)) == minimax (!p) t && (t :: ts).all (isPerfect (!p))

#eval do
  let mut runs := 0
  for k in [1, 2, 3, 4] do
    for d in [0, 1, 2, 3, 4, 5] do
      for i in [0:12] do
        -- even runs draw values from 1 .. 99, odd runs from 1 .. 4 (many ties)
        let m := if i % 2 == 0 then 99 else 4
        let p := i % 4 < 2
        let (_, t) := uniformTree k m (i * 7919 + 31 * k + d + 1) d
        let t := perfect p t
        unless isPerfect p t do throw (IO.userError s!"k={k} d={d} run {i}: not perfect")
        let r := alphaBeta p ⊥ ⊤ t
        let want := k ^ ((d + 1) / 2) + k ^ (d / 2) - 1
        unless r.ret == minimax p t && r.time == want do
          throw (IO.userError s!"k={k} d={d} run {i}: {r.time} leaves, expected {want}")
        runs := runs + 1
  IO.println s!"{runs} perfectly ordered uniform trees (k = 1..4, d = 0..5): \
    alpha-beta evaluates exactly k ^ ⌈d/2⌉ + k ^ ⌊d/2⌋ - 1 leaves"

/-! ## Ledger examples through the theorem -/

/-- `b = 2, d = 2`, perfectly ordered: the maximizer's first move is worth `3`, the second `2`. -/
private def best22 : GameTree V := .node [.node [.leaf 3, .leaf 5], .node [.leaf 2, .leaf 9]]

/-- The same leaves in the worst order. -/
private def worst22 : GameTree V := .node [.node [.leaf 9, .leaf 2], .node [.leaf 5, .leaf 3]]

/-- The maximizer's first move is worth `⊤`. -/
private def top22 : GameTree V := .node [.node [.leaf 100, .leaf 100], .node [.leaf 7, .leaf 8]]

private theorem uniform22 (a b c d : V) :
    Uniform 2 2 (.node [.node [.leaf a, .leaf b], .node [.leaf c, .leaf d]] : GameTree V) := by
  refine .node rfl ?_
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;>
  · refine .node rfl ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact .leaf _

private theorem best22_uniform : Uniform 2 2 best22 := uniform22 3 5 2 9

private theorem best22_ordered : PerfectlyOrdered true best22 := by
  refine .node (by decide) ?_
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;>
  · refine .node (by decide) ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact .leaf _ _

/-- Positive check: `b = 2, d = 2` gives `3`. -/
example : (alphaBeta true ⊥ ⊤ best22).time = 3 := by
  rw [alphaBeta_leafCount_perfect best22_uniform best22_ordered (by decide) (by decide)]

example : (alphaBeta true ⊥ ⊤ best22).time = 3 := by decide

/-- Nonvacuity: `d = 0` gives `1` for every branching factor. -/
example (k : ℕ) : (alphaBeta false ⊥ ⊤ (.leaf (50 : V))).time = 1 := by
  rw [alphaBeta_leafCount_perfect (k := k) (.leaf _) (.leaf _ _) (by decide) (by decide)]
  simp

/-- Negative check: the worst ordering evaluates all `b ^ d = 4` leaves. -/
example : (alphaBeta true ⊥ ⊤ worst22).time = 4 := by decide

example : ¬ PerfectlyOrdered true worst22 := by
  intro h
  cases h with
  | node hfirst _ => exact absurd hfirst (by decide)

/-- Boundary: with root value `⊤` the maximizer cuts after its first move. -/
example : (alphaBeta true ⊥ ⊤ top22).time = 2 := by decide

example : minimax true top22 = ⊤ := by decide

/-! ## Axioms -/

#print axioms alphaBeta_leafCount_perfect
#print axioms alphaBeta_time_pv
#print axioms alphaBeta_time_cut_all
#print axioms pvLeaves_succ_succ

end Cslib.Algorithms.Lean.AlphaBeta
