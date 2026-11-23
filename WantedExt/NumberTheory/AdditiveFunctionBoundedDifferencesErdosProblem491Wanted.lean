/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Additive functions with bounded differences (Erdős Problem 491)

Erdős Problem 491: if `f : ℕ → ℝ` is additive and `|f(n + 1) - f(n)| < c` for all `n`, must `f(n) =
c' log n + O(1)` for some `c'`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.AdditiveFunctionBoundedDifferencesErdosProblem491Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #491, https://www.erdosproblems.com/491 (status
PROVED). UnsolvedMath record UM-30006898 (`EP-491`), dataset ulamai/UnsolvedMath v1.8.0.

`f` lives on the positive integers (`f 0` is unconstrained); additivity is for coprime `a, b ≥ 1`;
`O(1)` is one bound `C` for all `n ≥ 1`. Compared with the formal-conjectures statement
`ErdosProblems/491.lean` (equivalent; it states `O(1)` with `=O[atTop]`; no code imported).
-/

/-- Erdős Problem 491: if `f` is additive on the positive integers (`f (a b) = f a + f b` for
coprime `a, b`) and `|f (n + 1) - f n| < c` for all `n ≥ 1`, then `f n = c' log n + O(1)`. -/
def boundedDifferenceAdditiveIsLog : Prop :=
  ∀ f : ℕ → ℝ, (∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → f (a * b) = f a + f b) →
    (∃ c : ℝ, ∀ n : ℕ, 0 < n → |f (n + 1) - f n| < c) →
      ∃ c' C : ℝ, ∀ n : ℕ, 0 < n → |f n - c' * Real.log n| ≤ C

/--
Resolved true: Wirsing proved that an additive function with bounded differences `f(n + 1) - f(n)`
is `c' log n + O(1)`. Source: T. F. Bloom, Erdős Problems, Problem #491,
https://www.erdosproblems.com/491 (status PROVED); resolution: E. Wirsing, A characterization of log
n as an additive arithmetic function, Symposia Math. (1970), 45-57, erdosproblems.com/491: true,
proved by Wirsing, https://www.erdosproblems.com/491.
-/
public theorem_wanted boundedDifferenceAdditiveIsLog_holds : boundedDifferenceAdditiveIsLog

end MathlibExt.NumberTheory.AdditiveFunctionBoundedDifferencesErdosProblem491Wanted
