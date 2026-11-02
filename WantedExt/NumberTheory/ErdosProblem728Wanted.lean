/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 728
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open Filter
open scoped Nat Topology

namespace MathlibExt.NumberTheory.ErdosProblem728Wanted

/-! Source record `FC-ErdosProblem728`, ported from FormalConjectures
`ErdosProblems/728.lean` (`theorem erdos_728`) and checked against
erdosproblems.com/728. The upstream `answer(True)` is dropped. Status:
resolved true externally by Barreto and ChatGPT-5.2. This module states the
result but does not prove it; a pinned external Lean proof is in the registry. -/

/-- **Erdős Problem 728.** The proposition that there is a real number $\delta > 0$ such that for
every real number $\varepsilon$ with $0 < \varepsilon < \delta$ and all real numbers $C > 0$ and
$C' > C$, there are natural numbers $a$, $b$ and $n \ge 1$ with $a > \varepsilon n$,
$b > \varepsilon n$, $a! \, b! \mid n! \, (a + b - n)!$ and $n + C \log n < a + b < n + C' \log n$.
-/
def conjecture : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
    ∃ a b n : ℕ,
      0 < n ∧
      ε * n < a ∧
      ε * n < b ∧
      a ! * b ! ∣ n ! * (a + b - n)! ∧
      a + b > n + C * Real.log n ∧
      a + b < n + C' * Real.log n

/--
**Erdős Problem 728 holds.** There is a real number $\delta > 0$ such that for every real number
$\varepsilon$ with $0 < \varepsilon < \delta$ and all real numbers $C > 0$ and $C' > C$, there are
natural numbers $a$, $b$ and $n \ge 1$ with $a > \varepsilon n$, $b > \varepsilon n$,
$a! \, b! \mid n! \, (a + b - n)!$ and $n + C \log n < a + b < n + C' \log n$.

The statement was resolved in the affirmative by Barreto and ChatGPT-5.2.

Source: N.
Sothanaphan, Resolution of Erdős Problem #728: a writeup of Aristotle's Lean proof,
arXiv:2601.07421 (2026), https://arxiv.org/abs/2601.07421. Moved from
`OpenConjectures/NumberTheory/ErdosProblem728`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem728Wanted
