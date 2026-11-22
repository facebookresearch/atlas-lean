/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.AlphaBeta
public meta import CSLibExt.Algorithms.Lean.GameTree.AlphaBeta
public import Mathlib.Order.Fin.Basic
public meta import Mathlib.Order.Fin.Basic

/-!
# Alpha-beta pruning tests

Executed fixtures, with values in `Fin 101` (`⊥ = 0`, `⊤ = 100`): each run compares alpha-beta
with the full window against the minimax value, checks the clamped agreement
(`alphaBeta_spec`) for every window `[a, b]` with `a ≤ b` drawn from a grid, and checks that
alpha-beta evaluates at most `leaves t` leaves; it throws otherwise. Fixtures: the three-ply tree of
Russell and Norvig (Figure 5.5, where a cutoff skips two leaves), a node without moves, a chain of
single moves, and 300 pseudo-random trees of depth up to 5. Closed checks instantiate the theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean

private abbrev V := Fin 101

private meta def lf (x : ℕ) : GameTree V := .leaf (Fin.ofNat 101 x)

/-- Run every check on one tree; returns the leaves evaluated with the full window. -/
private meta def check (label : String) (p : Bool) (t : GameTree V) (quiet : Bool := false) :
    IO Unit := do
  let m := minimax p t
  let r := alphaBeta p ⊥ ⊤ t
  unless r.ret == m && r.time ≤ leaves t do
    throw (IO.userError s!"{label}: alpha-beta {r.ret} (cost {r.time}), minimax {m}")
  for a in [0, 10, 25, 40, 50, 60, 75, 90, 100] do
    for b in [0, 10, 25, 40, 50, 60, 75, 90, 100] do
      if a ≤ b then
        let a' : V := Fin.ofNat 101 a
        let b' : V := Fin.ofNat 101 b
        let r' := alphaBeta p a' b' t
        unless max a' (min b' r'.ret) == max a' (min b' m) && r'.time ≤ leaves t do
          throw (IO.userError s!"{label}: window [{a}, {b}]: alpha-beta {r'.ret}, minimax {m}")
  unless quiet do
    IO.println s!"{label}: minimax {m}, alpha-beta {r.ret}, {r.time} of {leaves t} leaves"

-- Russell and Norvig, Figure 5.5: the second subtree is cut after its first leaf
#eval check "R&N Figure 5.5" true
  (.node [.node [lf 3, lf 12, lf 8], .node [lf 2, lf 4, lf 6], .node [lf 14, lf 5, lf 2]])
#eval check "no moves (maximizer)" true (.node [])
#eval check "no moves (minimizer)" false (.node [])
#eval check "chain of single moves" true (.node [.node [.node [.node [lf 42]]]])
#eval check "deep cutoff" true
  (.node [.node [.node [lf 5, lf 6], .node [lf 7, lf 4, lf 5]],
    .node [.node [lf 3]], .node [.node [lf 6], .node [lf 6, lf 9]]])

/-- A pseudo-random tree from seed `s`, branching 1 to 3, depth at most `d`. -/
private meta def rand (s : ℕ) : ℕ → ℕ × GameTree V
  | 0 => ((s * 1103515245 + 12345) % 2147483648, lf (s % 101))
  | d + 1 =>
    let s := (s * 1103515245 + 12345) % 2147483648
    if s % 6 == 0 then (s, lf (s / 7 % 101)) else
    let k := 1 + s / 11 % 3
    let (s, ts) := (List.range k).foldl (fun (acc : ℕ × List (GameTree V)) _ =>
      let (s', t) := rand acc.1 d
      (s', acc.2 ++ [t])) (s, [])
    (s, .node ts)

#eval do
  let mut saved := 0
  let mut total := 0
  for i in [0:300] do
    let (_, t) := rand (i * 7919 + 1) 5
    check s!"random {i}" (i % 2 == 0) t (quiet := true)
    saved := saved + (leaves t - (alphaBeta (i % 2 == 0) ⊥ ⊤ t).time)
    total := total + leaves t
  IO.println s!"300 pseudo-random trees: agree with minimax on every window; \
    {total - saved} of {total} leaves evaluated"

/-! Closed checks -/

example (p : Bool) (t : GameTree V) : (alphaBeta p ⊥ ⊤ t).ret = minimax p t :=
  alphaBeta_bot_top p t

example (p : Bool) (a b : V) (t : GameTree V) (hab : a ≤ b) :
    max a (min b (alphaBeta p a b t).ret) = max a (min b (minimax p t)) :=
  alphaBeta_spec p a b t hab

#print axioms alphaBeta_spec
#print axioms alphaBeta_bot_top
#print axioms alphaBeta_le_of_minimax_le
#print axioms alphaBeta_eq_of_mem_window
#print axioms le_alphaBeta_of_le_minimax
#print axioms alphaBeta_time_le

end Cslib.Algorithms.Lean.AlphaBeta
