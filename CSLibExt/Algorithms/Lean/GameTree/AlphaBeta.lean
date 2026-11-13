/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.MinMax
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.Order

/-!
# Alpha-beta pruning returns the minimax value

A finite game tree (`GameTree`) has leaves carrying the value of a terminal position and inner
nodes listing the positions reachable in one move. Values lie in a bounded linear order: a
position without moves is worth `⊥` to the maximizer and `⊤` to the minimizer. `minimax p t` is
the value of `t` when player `p` moves (`true` for the maximizer).

`alphaBeta p a b t` is alpha-beta pruning (Knuth and Moore, *An analysis of alpha-beta pruning*,
Artificial Intelligence 6 (1975), procedure F2; Russell and Norvig, *Artificial Intelligence: A
Modern Approach*, fourth edition, Section 5.3): the maximizer raises `a` to the best value found so
far among the children and stops scanning as soon as `b ≤ a` (a cutoff); the minimizer lowers `b`
and stops as soon as `b ≤ a`. Main results:

* `alphaBeta_spec`: for `a ≤ b`, the result agrees with the minimax value after clamping to
  `[a, b]`, `max a (min b (alphaBeta p a b t).ret) = max a (min b (minimax p t))`. Equivalently
  (Knuth and Moore's conditions): a value at most `a` is reported as at most `a`, a value strictly
  inside the window exactly, and a value at least `b` as at least `b`
  (`alphaBeta_le_of_minimax_le`, `alphaBeta_eq_of_mem_window`, `le_alphaBeta_of_le_minimax`, for
  `a < b`).
* `alphaBeta_bot_top`: with the full window, `(alphaBeta p ⊥ ⊤ t).ret = minimax p t`.
* `alphaBeta_time_le`: alpha-beta evaluates at most `leaves t` leaves, the number plain minimax
  evaluates.

## Cost model

`alphaBeta` runs in `TimeM` and charges one unit per leaf evaluated (one call of the static
evaluation function); comparisons, `max`/`min` and the traversal itself are free. Plain minimax
evaluates every leaf, `leaves t` units; alpha-beta never evaluates more (`alphaBeta_time_le`), and
the tests show trees where a cutoff saves evaluations.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean

universe u

/-- **Game tree.** A game tree with values in a type $\alpha$ is either a leaf, which carries a
value in $\alpha$ (the value of a terminal position), or an inner node, which carries a finite
list of game trees (the positions reachable in one move; the list may be empty). Game trees are
built inductively, so every game tree is finite. -/
inductive GameTree (α : Type u) where
  | leaf : α → GameTree α
  | node : List (GameTree α) → GameTree α

variable {α : Type u}

mutual
/-- **Number of leaves.** The number of leaves of a game tree is defined recursively: a leaf counts
$1$, and an inner node counts the total number of leaves of its children (so an inner node without
children counts $0$). -/
def leaves : GameTree α → ℕ
  | .leaf _ => 1
  | .node ts => leavesList ts

/-- **Number of leaves of a list of game trees.** The number of leaves of a finite list of game
trees is the sum of the numbers of leaves of its members ($0$ for the empty list). -/
def leavesList : List (GameTree α) → ℕ
  | [] => 0
  | t :: ts => leaves t + leavesList ts
end

variable [LinearOrder α]

mutual
/-- **Alpha-beta pruning.** For a player $p$ to move and values $a$ and $b$ in a linear order,
alpha-beta pruning with window $[a, b]$ returns the value of a leaf at a cost of one unit (one
leaf evaluation), and on an inner node runs the alpha-beta scan of its children for $p$ with
window $[a, b]$. -/
def alphaBeta : Bool → α → α → GameTree α → TimeM ℕ α
  | _, _, _, .leaf x => do
      TimeM.tick 1
      pure x
  | p, a, b, .node ts => alphaBetaList p a b ts

/-- **Alpha-beta scan of the children.** Given the player $p$ to move, values $a$ and $b$ in a
linear order and a list of game trees (the children of a position), the scan runs alpha-beta
pruning for the other player on the children in order, each time with the current bounds $a$ and
$b$. The maximizer replaces $a$ by $\max(a, v)$, where $v$ is the child's returned value, and
stops as soon as $b \le a$, returning the new $a$; if it never stops early it returns the final
$a$ ($a$ itself for an empty list). The minimizer replaces $b$ by $\min(b, v)$ and stops as soon
as $b \le a$, returning the new $b$; if it never stops early it returns the final $b$ ($b$ itself
for an empty list). The cost of the scan is the total cost of the children it evaluates. -/
def alphaBetaList : Bool → α → α → List (GameTree α) → TimeM ℕ α
  | true, a, _, [] => pure a
  | false, _, b, [] => pure b
  | true, a, b, t :: ts => do
      let v ← alphaBeta false a b t
      let a' := max a v
      if b ≤ a' then pure a' else alphaBetaList true a' b ts
  | false, a, b, t :: ts => do
      let v ← alphaBeta true a b t
      let b' := min b v
      if b' ≤ a then pure b' else alphaBetaList false a b' ts
end

/-! ## Scan bounds and order facts -/

/-- **Lower bound for the maximizer's scan.** Let values lie in a linear order. For all values $a$
and $b$ and every finite list of game trees, the value returned by the alpha-beta scan of the list
with the maximizer to move and window $[a, b]$ is at least $a$. -/
theorem le_alphaBetaList_true (a b : α) :
    ∀ ts : List (GameTree α), a ≤ (alphaBetaList true a b ts).ret
  | [] => le_refl a
  | t :: ts => by
      simp only [alphaBetaList, TimeM.ret_bind]
      split_ifs
      · exact le_max_left _ _
      · exact (le_max_left a _).trans (le_alphaBetaList_true _ b ts)

/-- **The minimizer's alpha-beta scan stays at or below its upper bound.** For all values $a, b$ in
a linear order and every list $ts$ of game trees, the value returned by the alpha-beta scan of
$ts$ for the minimizer with lower bound $a$ and upper bound $b$ is at most $b$. -/
theorem alphaBetaList_false_le (a b : α) :
    ∀ ts : List (GameTree α), (alphaBetaList false a b ts).ret ≤ b
  | [] => le_refl b
  | t :: ts => by
      simp only [alphaBetaList, TimeM.ret_bind]
      split_ifs
      · exact min_le_left _ _
      · exact (alphaBetaList_false_le a _ ts).trans (min_le_left b _)

private theorem max_cut (a b v m L : α) (hab : a ≤ b)
    (ih : max a (min b v) = max a (min b m)) (hc : b ≤ max a v) :
    max a (min b (max a v)) = max a (min b (max m L)) := by
  simp only [max_def, min_def] at *
  split_ifs at * <;> order

private theorem max_rec (a b v m L r : α) (hab : a ≤ b)
    (ih : max a (min b v) = max a (min b m)) (hr : max a v ≤ r)
    (h : max (max a v) (min b r) = max (max a v) (min b L)) :
    max a (min b r) = max a (min b (max m L)) := by
  simp only [max_def, min_def] at *
  split_ifs at * <;> order

private theorem min_cut (a b v m L : α) (hab : a ≤ b)
    (ih : max a (min b v) = max a (min b m)) (hc : min b v ≤ a) :
    max a (min b (min b v)) = max a (min b (min m L)) := by
  simp only [max_def, min_def] at *
  split_ifs at * <;> order

private theorem min_rec (a b v m L r : α)
    (ih : max a (min b v) = max a (min b m)) (hc : a < min b v) (hr : r ≤ min b v)
    (h : max a (min (min b v) r) = max a (min (min b v) L)) :
    max a (min b r) = max a (min b (min m L)) := by
  rw [min_eq_right hr] at h
  rw [min_eq_right (hr.trans (min_le_left _ _)), ← min_assoc]
  have h3 : min b m = min b v := by
    rw [max_eq_right hc.le] at ih
    rcases le_total (min b m) a with h' | h'
    · rw [max_eq_left h'] at ih; exact absurd ih (ne_of_lt hc).symm
    · rw [max_eq_right h'] at ih; exact ih.symm
  rw [h3]; exact h

/-! ## Cost -/

mutual
/-- **Alpha-beta never evaluates more leaves than the tree has.** For either player $p$ to move
and all values $a, b$ in a linear order, alpha-beta pruning run on a game tree $t$ for $p$ with
window $[a, b]$ evaluates at most as many leaves as $t$ has, each leaf evaluation costing one
unit. -/
theorem alphaBeta_time_le : ∀ (p : Bool) (a b : α) (t : GameTree α),
    (alphaBeta p a b t).time ≤ leaves t
  | _, _, _, .leaf x => by simp [alphaBeta, leaves]
  | p, a, b, .node ts => by
      simp only [alphaBeta, leaves]
      exact alphaBetaList_time_le p a b ts

/-- **Cost of the alpha-beta scan.** For either player $p$, all values $a, b$ in a linear order
and every list $ts$ of game trees, the alpha-beta scan of $ts$ for $p$ with lower bound $a$ and
upper bound $b$ evaluates at most as many leaves as the trees in $ts$ have in total, each leaf
evaluation costing one unit. -/
theorem alphaBetaList_time_le : ∀ (p : Bool) (a b : α) (ts : List (GameTree α)),
    (alphaBetaList p a b ts).time ≤ leavesList ts
  | true, _, _, [] => by simp [alphaBetaList, leavesList]
  | false, _, _, [] => by simp [alphaBetaList, leavesList]
  | true, a, b, t :: ts => by
      have h1 := alphaBeta_time_le false a b t
      have h2 := alphaBetaList_time_le true (max a (alphaBeta false a b t).ret) b ts
      simp only [alphaBetaList, leavesList, TimeM.time_bind]
      split_ifs <;> (try simp only [TimeM.time_pure]) <;> omega
  | false, a, b, t :: ts => by
      have h1 := alphaBeta_time_le true a b t
      have h2 := alphaBetaList_time_le false a (min b (alphaBeta true a b t).ret) ts
      simp only [alphaBetaList, leavesList, TimeM.time_bind]
      split_ifs <;> (try simp only [TimeM.time_pure]) <;> omega
end

/-! ## The minimax value; from here on the order is bounded -/

variable [BoundedOrder α]

mutual
/-- **Minimax value.** Let values lie in a bounded linear order. The minimax value of a game tree
with player $p$ to move (the maximizer or the minimizer) is defined recursively: a leaf is worth
the value it carries; an inner node is worth, for the maximizer, the maximum of the minimax values
of its children with the minimizer to move, and for the minimizer, the minimum of the minimax
values of its children with the maximizer to move. An inner node without children is worth $\bot$
to the maximizer and $\top$ to the minimizer. -/
def minimax : Bool → GameTree α → α
  | _, .leaf x => x
  | p, .node ts => minimaxList p ts

/-- **Minimax value of a list of positions.** Let values lie in a bounded linear order. For a player
$p$ and a finite list of game trees, the value for $p$ is the best of their minimax values with the
other player to move: for the maximizer, the maximum of these values, or $\bot$ if the list is
empty; for the minimizer, the minimum of these values, or $\top$ if the list is empty. -/
def minimaxList : Bool → List (GameTree α) → α
  | true, [] => ⊥
  | false, [] => ⊤
  | true, t :: ts => max (minimax false t) (minimaxList true ts)
  | false, t :: ts => min (minimax true t) (minimaxList false ts)
end

/-! ## Correctness -/

mutual
/-- **Alpha-beta is correct** (Knuth and Moore 1975, Theorem 1): for `a ≤ b`, the result of
alpha-beta agrees with the minimax value after clamping both to the window `[a, b]`. -/
theorem alphaBeta_spec : ∀ (p : Bool) (a b : α) (t : GameTree α), a ≤ b →
    max a (min b (alphaBeta p a b t).ret) = max a (min b (minimax p t))
  | _, _, _, .leaf x, _ => by simp [alphaBeta, minimax]
  | p, a, b, .node ts, h => by
      simp only [alphaBeta, minimax]
      exact alphaBetaList_spec p a b ts h

/-- **Correctness of the alpha-beta scan.** Let $p$ be the player to move, $ts$ a list of game
trees with values in a bounded linear order, and $a \le b$. Let $r$ be the value returned by the
alpha-beta scan of $ts$ for $p$ with window $[a, b]$, and let $m$ be the best value for $p$ among
$ts$: the maximum of the minimax values of the trees in $ts$ for the minimizer ($\bot$ if $ts$ is
empty) when $p$ is the maximizer, and the minimum of their minimax values for the maximizer
($\top$ if $ts$ is empty) when $p$ is the minimizer. Then $\max(a, \min(b, r)) =
\max(a, \min(b, m))$. -/
theorem alphaBetaList_spec : ∀ (p : Bool) (a b : α) (ts : List (GameTree α)), a ≤ b →
    max a (min b (alphaBetaList p a b ts).ret) = max a (min b (minimaxList p ts))
  | true, a, b, [], h => by simp [alphaBetaList, minimaxList, h]
  | false, a, b, [], h => by simp [alphaBetaList, minimaxList, h]
  | true, a, b, t :: ts, h => by
      have ih := alphaBeta_spec false a b t h
      simp only [alphaBetaList, minimaxList, TimeM.ret_bind]
      split_ifs with hc
      · exact max_cut a b _ _ _ h ih hc
      · have hlt : max a (alphaBeta false a b t).ret ≤ b := le_of_lt (not_le.1 hc)
        exact max_rec a b _ _ _ _ h ih (le_alphaBetaList_true _ b ts)
          (alphaBetaList_spec true _ b ts hlt)
  | false, a, b, t :: ts, h => by
      have ih := alphaBeta_spec true a b t h
      simp only [alphaBetaList, minimaxList, TimeM.ret_bind]
      split_ifs with hc
      · exact min_cut a b _ _ _ h ih hc
      · have hlt : a < min b (alphaBeta true a b t).ret := not_le.1 hc
        exact min_rec a b _ _ _ _ ih hlt (alphaBetaList_false_le a _ ts)
          (alphaBetaList_spec false a _ ts hlt.le)
end

/-- **Alpha-beta fails low when the minimax value is at most the lower bound.** Let $t$ be a game
tree with values in a bounded linear order, $p$ the player to move and $a < b$ values. If the
minimax value of $t$ for $p$ is at most $a$, then alpha-beta pruning run on $t$ for $p$ with the
window $[a, b]$ returns a value at most $a$. -/
theorem alphaBeta_le_of_minimax_le {p : Bool} {a b : α} {t : GameTree α} (hab : a < b)
    (h : minimax p t ≤ a) : (alphaBeta p a b t).ret ≤ a := by
  have := alphaBeta_spec p a b t hab.le
  simp only [max_def, min_def] at *
  split_ifs at * <;> order

/-- **Alpha-beta is exact inside the window.** Let $t$ be a game tree with values in a bounded
linear order, $p$ the player to move and $a, b$ values. If the minimax value $v$ of $t$ for $p$
satisfies $a < v < b$, then alpha-beta pruning run on $t$ for $p$ with the window $[a, b]$ returns
exactly $v$. -/
theorem alphaBeta_eq_of_mem_window {p : Bool} {a b : α} {t : GameTree α}
    (ha : a < minimax p t) (hb : minimax p t < b) : (alphaBeta p a b t).ret = minimax p t := by
  have := alphaBeta_spec p a b t (le_of_lt (ha.trans hb))
  simp only [max_def, min_def] at *
  split_ifs at * <;> order

/-- **Alpha-beta at or above the top of the window.** Let values lie in a bounded linear order, let
$t$ be a game tree, let $p$ be a player, and let $a < b$. If the minimax value of $t$ with $p$ to
move is at least $b$, then the value returned by alpha-beta pruning on $t$ with $p$ to move and
window $[a, b]$ is at least $b$. -/
theorem le_alphaBeta_of_le_minimax {p : Bool} {a b : α} {t : GameTree α} (hab : a < b)
    (h : b ≤ minimax p t) : b ≤ (alphaBeta p a b t).ret := by
  have := alphaBeta_spec p a b t hab.le
  simp only [max_def, min_def] at *
  split_ifs at * <;> order

/-- **Alpha-beta with the full window returns the minimax value.** Let $t$ be a game tree whose
values lie in a bounded linear order with least element $\bot$ and greatest element $\top$. For
either player $p$ to move, alpha-beta pruning run on $t$ for $p$ with the window $[\bot, \top]$
returns exactly the minimax value of $t$ for $p$. -/
theorem alphaBeta_bot_top (p : Bool) (t : GameTree α) :
    (alphaBeta p ⊥ ⊤ t).ret = minimax p t := by
  simpa using alphaBeta_spec p ⊥ ⊤ t bot_le

end Cslib.Algorithms.Lean.AlphaBeta
