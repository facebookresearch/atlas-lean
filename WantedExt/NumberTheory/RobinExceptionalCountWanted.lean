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

/-- **Robin exceptional set.** For a real number $x$, the Robin exceptional set up to $x$ is the
set of natural numbers $n$ with $7! = 5040 < n \le x$ that fail Robin's inequality, that is,
with $\sigma(n) \ge e^\gamma n \log\log n$, where $\sigma(n)$ is the sum of the divisors of $n$
and $\gamma$ is the Euler–Mascheroni constant. Its cardinality is the counting function $N_R(x)$.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Section 1. -/
public noncomputable def robinExceptionalSet (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 5040 ⌊x⌋₊).filter fun n =>
    Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
      (ArithmeticFunction.sigma 1 n : ℝ)

/-- **The Robin exceptional set is empty up to $7!$.** For every real $x \le 7! = 5040$, the
Robin exceptional set up to $x$ is empty; that is, its cardinality $N_R(x)$ is $0$.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Section 1 (definition of `N_R(x)`). -/
public theorem robinExceptionalSet_eq_empty_of_le {x : ℝ} (hx : x ≤ 5040) :
    robinExceptionalSet x = ∅ := by
  have h : ⌊x⌋₊ ≤ 5040 := Nat.floor_le_of_le (by exact_mod_cast hx)
  simp [robinExceptionalSet, Finset.Ioc_eq_empty_of_le h]

/-- **Failures of Robin's inequality number $O(x/\log\log x)$.** Let $N_R(x)$ be the number of
elements of the Robin exceptional set up to $x$. Then $N_R(x) = O(x / \log\log x)$ as the real
number $x$ tends to infinity.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 1 (`integers-2025-A8-thm-1`). -/
public theorem_wanted card_robinExceptionalSet_isBigO_div_log_log :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop]
      fun x : ℝ => x / Real.log (Real.log x)

/-- **Failures of Robin's inequality number $O(x/\sqrt{\log x})$.** Let $N_R(x)$ be the number
of elements of the Robin exceptional set up to $x$. Then $N_R(x) = O(x / \sqrt{\log x})$ as the
real number $x$ tends to infinity.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 2 (`integers-2025-A8-thm-2`). -/
public theorem_wanted card_robinExceptionalSet_isBigO_div_sqrt_log :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop]
      fun x : ℝ => x / Real.sqrt (Real.log x)

/-- **Failures of Robin's inequality number $O(x^\varepsilon)$.** Let $N_R(x)$ be the number of
elements of the Robin exceptional set up to $x$. For every real $\varepsilon > 0$,
$N_R(x) = O(x^\varepsilon)$ as the real number $x$ tends to infinity.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 3 (`integers-2025-A8-thm-3`). -/
public theorem_wanted card_robinExceptionalSet_isBigO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop] fun x : ℝ => x ^ ε

end

end MetaMathlibExt
