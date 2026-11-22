/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting sums of two squarefull numbers (Erdős Problem 1081)

Erdős Problem 1081: let `A(x)` count the `n ≤ x` which are the sum of two squarefull numbers. Is it
true that `A(x) ∼ c x / (log x)^{1/2}` for some `c > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.KFull

@[expose] public section

namespace MathlibExt.NumberTheory.SumsOfTwoSquarefullErdosProblem1081Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1081, https://www.erdosproblems.com/1081 (status
DISPROVED). UnsolvedMath record UM-30007158 (`EP-1081`), dataset ulamai/UnsolvedMath v1.8.0.

Squarefull is `MathlibExt`'s `Nat.IsKFull 2` (`m ≠ 0` and `p ∣ m → p² ∣ m` for every prime `p`;
`1` is squarefull); allowing `0` would add only the squarefull numbers themselves, `O(x^{1/2})` of
them. `x` runs through the natural numbers.
-/

/-- `A(x)`: the number of `n ≤ x` that are the sum of two squarefull numbers. -/
noncomputable def sumTwoSquarefullCount (x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ a b, Nat.IsKFull 2 a ∧ Nat.IsKFull 2 b ∧ n = a + b}.ncard

/-- Erdős Problem 1081: `A(x) ∼ c x / (log x)^{1/2}` for some `c > 0`. -/
def sumTwoSquarefullAsymptotic : Prop :=
  ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
    (fun x : ℕ => (sumTwoSquarefullCount x : ℝ) / (c * x / Real.sqrt (Real.log x)))
    Filter.atTop (nhds 1)

/--
Resolved false: Odoni disproved it, and Blomer and Granville proved `A(x) = (log log x)^{O(1)} x /
(log x)^α` with `α = 1 - 2^{-1/3} < 1/2`, so `A(x) / (x / (log x)^{1/2}) → ∞`;
erdosproblems.com/1081 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#1081, https://www.erdosproblems.com/1081 (status DISPROVED); resolution: R. W. K. Odoni, A problem
of Erdős on sums of two squarefull numbers, Acta Arith. (1981), 145-162; V. Blomer and A. Granville,
Estimates for representation numbers of quadratic forms, Duke Math. J. (2006), 261-302, Odoni
disproved it; Blomer-Granville: A(x) = (log log x)^{O(1)} x / (log x)^α with α = 1 - 2^{-1/3} ≈
0.2063 (erdosproblems.com/1081), https://www.erdosproblems.com/1081.
-/
public theorem_wanted sumTwoSquarefullAsymptotic_refuted : ¬ sumTwoSquarefullAsymptotic

end MathlibExt.NumberTheory.SumsOfTwoSquarefullErdosProblem1081Wanted
