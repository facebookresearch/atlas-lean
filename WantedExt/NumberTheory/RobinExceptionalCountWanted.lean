/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Counting failures of Robin's inequality (statements)

Statement-only targets from Florian Luca and Patrick Solé, *On Robin's Inequality*,
INTEGERS 25 (2025), Article A8: upper bounds for the number of `7! < n ≤ x` with
`σ(n) ≥ e^γ n log log n`. Robin's criterion makes this set empty under the Riemann Hypothesis;
the bounds here are unconditional.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- The set `{7! < n ≤ x : σ(n) ≥ e^γ n log log n}` of integers above `7! = 5040` up to `x`
failing Robin's inequality; its cardinality is the paper's counting function `N_R(x)`.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Section 1. -/
public noncomputable def robinExceptionalSet (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 5040 ⌊x⌋₊).filter fun n =>
    Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
      (ArithmeticFunction.sigma 1 n : ℝ)

/-- The exceptional set is empty for `x ≤ 7!`, i.e. `N_R(x) = 0` there.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Section 1 (definition of `N_R(x)`). -/
public theorem robinExceptionalSet_eq_empty_of_le {x : ℝ} (hx : x ≤ 5040) :
    robinExceptionalSet x = ∅ := by
  have h : ⌊x⌋₊ ≤ 5040 := Nat.floor_le_of_le (by exact_mod_cast hx)
  simp [robinExceptionalSet, Finset.Ioc_eq_empty_of_le h]

/-- Theorem 1: `N_R(x) = O(x / log log x)`, with `N_R(x)` the cardinality of
`robinExceptionalSet x`.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 1 (`integers-2025-A8-thm-1`). -/
public theorem_wanted card_robinExceptionalSet_isBigO_div_log_log :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop]
      fun x : ℝ => x / Real.log (Real.log x)

/-- Theorem 2: `N_R(x) = O(x / sqrt (log x))`, with `N_R(x)` the cardinality of
`robinExceptionalSet x`.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 2 (`integers-2025-A8-thm-2`). -/
public theorem_wanted card_robinExceptionalSet_isBigO_div_sqrt_log :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop]
      fun x : ℝ => x / Real.sqrt (Real.log x)

/-- Theorem 3: `N_R(x) = O(x^ε)` for every `ε > 0`, with `N_R(x)` the cardinality of
`robinExceptionalSet x`.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 3 (`integers-2025-A8-thm-3`). -/
public theorem_wanted card_robinExceptionalSet_isBigO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop] fun x : ℝ => x ^ ε

end

end MetaMathlibExt
