/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.RobinExceptionalCount

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
