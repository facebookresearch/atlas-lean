/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Algorithms.Lean.GameTree.AlphaBeta
public import Mathlib.Order.Fin.Basic

/-!
These examples pin the boundary behaviour of the native `alphaBeta` search on
`Fin 11` leaves. The raw result is not clamped to the search window, while
`alphaBeta_spec` compares both sides after clamping.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

/-- Out-of-window leaf: the raw result keeps the leaf value `10` outside `[0, 1]`. -/
example : (alphaBeta true (0 : Fin 11) (1 : Fin 11) (.leaf (10 : Fin 11))).ret = 10 := rfl

/-- Out-of-window leaf: clamping the raw result to `[0, 1]` yields `1`. -/
example : max (0 : Fin 11) (min (1 : Fin 11)
    (alphaBeta true (0 : Fin 11) (1 : Fin 11) (.leaf (10 : Fin 11))).ret) = 1 := by decide

/-- Out-of-window leaf: the raw result differs from the clamped minimax value. -/
example : (alphaBeta true (0 : Fin 11) (1 : Fin 11) (.leaf (10 : Fin 11))).ret ≠
    max (0 : Fin 11) (min (1 : Fin 11) (minimax true (.leaf (10 : Fin 11)))) := by decide

/-- Full window: the raw result equals the minimax value for every leaf. -/
example (x : Fin 11) : (alphaBeta true (⊥ : Fin 11) (⊤ : Fin 11) (.leaf x)).ret =
    minimax true (.leaf x) :=
  alphaBeta_bot_top true (.leaf x)

/-- In-window leaf: the raw result equals the leaf value `5` inside `[0, 10]`. -/
example : (alphaBeta true (0 : Fin 11) (10 : Fin 11) (.leaf (5 : Fin 11))).ret = 5 := by
  have ha : (0 : Fin 11) < minimax true (.leaf (5 : Fin 11)) := by decide
  have hb : minimax true (.leaf (5 : Fin 11)) < (10 : Fin 11) := by decide
  exact alphaBeta_eq_of_mem_window ha hb

#print axioms alphaBeta_spec
#print axioms alphaBeta_bot_top
#print axioms alphaBeta_eq_of_mem_window
#print axioms alphaBeta_le_of_minimax_le
#print axioms le_alphaBeta_of_le_minimax
#print axioms alphaBeta_time_le

end Cslib.Algorithms.Lean.AlphaBeta
