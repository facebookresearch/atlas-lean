/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic

/-!
# Iterated elimination of weakly dominated pure strategies

A restriction of a two-player game keeps a finite set of rows and a finite set of columns.
Each player maximises their own component of the payoff pair. A comparison uses the pointwise
order on payoff vectors indexed by the *surviving* opponent strategies: by `Pi.lt_def`, strict
inequality in this order means weak inequality everywhere and strict inequality somewhere.

The two maximal deletion sequences in `iteratedWeakDominance_depends_on_order` start at the
same three-by-two game. Their terminal rectangles have different profiles and payoff images.
-/

@[expose] public section

namespace MathlibExt.GameTheory

open Finset Relation

variable {R C α β : Type*} [DecidableEq R] [DecidableEq C] [Preorder α] [Preorder β]

/-- One deletion in a two-player pure-strategy game with preordered payoffs `u` (row payoff
first, column payoff second; both players maximise). A state is a pair of finite sets of
surviving strategies. Erase exactly one surviving row or column: another surviving strategy
of that player must pay at least as much against every surviving opponent strategy and
strictly more against at least one. In particular, an everywhere-tied alternative does not
justify deletion. -/
inductive WeakDominanceStep (u : R × C → α × β) :
    Finset R × Finset C → Finset R × Finset C → Prop where
  /-- Erase only row `r`: the surviving row `r'` gives the row player at least as much at
  every surviving column and strictly more at some surviving column. -/
  | row {rows : Finset R} {cols : Finset C} {r r' : R} (hr : r ∈ rows) (hr' : r' ∈ rows)
      (better : (fun c : cols ↦ (u (r, c)).1) < fun c : cols ↦ (u (r', c)).1) :
      WeakDominanceStep u (rows, cols) (rows.erase r, cols)
  /-- Erase only column `c`: the surviving column `c'` gives the column player at least as
  much at every surviving row and strictly more at some surviving row. -/
  | col {rows : Finset R} {cols : Finset C} {c c' : C} (hc : c ∈ cols) (hc' : c' ∈ cols)
      (better : (fun r : rows ↦ (u (r, c)).2) < fun r : rows ↦ (u (r, c')).2) :
      WeakDominanceStep u (rows, cols) (rows, cols.erase c)

/-- A rectangle of surviving pure strategies on which the payoff pair is constant is terminal
for single-strategy weak dominance deletion: neither player can improve strictly against even
one surviving opponent strategy. The two payoff orders need only be preorders. -/
theorem not_weakDominanceStep_of_constant {u : R × C → α × β} {rows : Finset R}
    {cols : Finset C} {v : α × β} (h : ∀ r ∈ rows, ∀ c ∈ cols, u (r, c) = v)
    (next : Finset R × Finset C) : ¬ WeakDominanceStep u (rows, cols) next := by
  intro step
  cases step with
  | row hr hr' better =>
    exact better.ne (funext fun c ↦ congrArg Prod.fst ((h _ hr _ c.2).trans (h _ hr' _ c.2).symm))
  | col hc hc' better =>
    exact better.ne (funext fun r ↦ congrArg Prod.snd ((h _ r.2 _ hc).trans (h _ r.2 _ hc').symm))

/-- Payoffs of a three-by-two pure-strategy game, in (row player, column player) order;
rows `0, 1, 2` are T, M, B and columns `0, 1` are L, R. In left-to-right column order the
three rows are `[(1,1), (0,0)]`, `[(1,1), (2,1)]` and `[(0,0), (2,1)]`. -/
def orderDependencePayoff : Fin 3 × Fin 2 → ℕ × ℕ
  | (0, 0) => (1, 1)
  | (0, 1) => (0, 0)
  | (1, 0) => (1, 1)
  | (1, 1) => (2, 1)
  | (2, 0) => (0, 0)
  | (2, 1) => (2, 1)

/-- Iterated elimination of weakly dominated pure strategies can depend on the deletion order.
In the three-by-two game with rows T, M, B and columns L, R, the payoff pairs in each row are
`[(1,1), (0,0)]`, `[(1,1), (2,1)]` and `[(0,0), (2,1)]`, respectively. Both players maximise.
Starting from all strategies, delete one surviving strategy at a time using a surviving pure
alternative that is no worse against every surviving opponent strategy and better against at
least one. M can eliminate either T or B. Deleting T then L leaves `{M,B} × {R}` with payoff
image `{(2,1)}`; deleting B then R leaves `{T,M} × {L}` with payoff image `{(1,1)}`. Neither
rectangle admits another deletion, and both the surviving profile sets and their payoff images
differ. -/
theorem iteratedWeakDominance_depends_on_order :
    let full : Finset (Fin 3) × Finset (Fin 2) := (univ, univ)
    let right : Finset (Fin 3) × Finset (Fin 2) := ({1, 2}, {1})
    let left : Finset (Fin 3) × Finset (Fin 2) := ({0, 1}, {0})
    let step := WeakDominanceStep orderDependencePayoff
    let X := right.1.product right.2
    let Y := left.1.product left.2
    ReflTransGen step full right ∧ ReflTransGen step full left ∧
      (∀ next, ¬ step right next) ∧ (∀ next, ¬ step left next) ∧ X ≠ Y ∧
      X.image orderDependencePayoff = {(2, 1)} ∧ Y.image orderDependencePayoff = {(1, 1)} ∧
      X.image orderDependencePayoff ≠ Y.image orderDependencePayoff := by
  intro full right left step X Y
  have dropT : step full ({1, 2}, univ) := by
    rw [show ({1, 2} : Finset (Fin 3)) = univ.erase 0 by decide]
    exact .row (mem_univ 0) (mem_univ 1) (Pi.lt_def.mpr (by decide))
  have dropL : step ({1, 2}, univ) right := by
    change WeakDominanceStep _ ({1, 2}, univ) ({1, 2}, {1})
    rw [show ({1} : Finset (Fin 2)) = univ.erase 0 by decide]
    exact .col (mem_univ 0) (mem_univ 1) (Pi.lt_def.mpr (by decide))
  have dropB : step full ({0, 1}, univ) := by
    rw [show ({0, 1} : Finset (Fin 3)) = univ.erase 2 by decide]
    exact .row (mem_univ 2) (mem_univ 1) (Pi.lt_def.mpr (by decide))
  have dropR : step ({0, 1}, univ) left := by
    change WeakDominanceStep _ ({0, 1}, univ) ({0, 1}, {0})
    rw [show ({0} : Finset (Fin 2)) = univ.erase 1 by decide]
    exact .col (mem_univ 1) (mem_univ 0) (Pi.lt_def.mpr (by decide))
  exact ⟨(ReflTransGen.single dropT).tail dropL, (ReflTransGen.single dropB).tail dropR,
    not_weakDominanceStep_of_constant (v := (2, 1)) (by decide),
    not_weakDominanceStep_of_constant (v := (1, 1)) (by decide), by decide, by decide,
    by decide, by decide⟩

end MathlibExt.GameTheory
