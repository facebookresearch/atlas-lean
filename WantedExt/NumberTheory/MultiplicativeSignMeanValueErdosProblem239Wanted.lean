/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mean values of multiplicative `±1` functions (Erdős Problem 239)

Erdős Problem 239: let `f : ℕ → {-1, 1}` be multiplicative. Does `lim_{N → ∞} (1/N) ∑_{n ≤ N} f(n)`
always exist?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.MultiplicativeSignMeanValueErdosProblem239Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #239, https://www.erdosproblems.com/239 (status PROVED
(LEAN)). UnsolvedMath record UM-30006787 (`EP-239`), dataset ulamai/UnsolvedMath v1.8.0.

Multiplicative means `f(1) = 1` and `f(mn) = f(m) f(n)` for coprime `m, n`; the values on `n ≥ 1`
are `±1` and `f(0)` is unused. Compared with the formal-conjectures statement
`ErdosProblems/239.lean` (equivalent; no code imported).
-/

open Filter Topology

/-- Erdős Problem 239: for every multiplicative `f : ℕ → {-1, 1}` the mean
`(1/N) ∑_{n ≤ N} f(n)` converges as `N → ∞`. -/
def multiplicativeSignMeanConverges : Prop :=
  ∀ f : ℕ → ℝ, f 1 = 1 → (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    (∀ n : ℕ, 1 ≤ n → f n = 1 ∨ f n = -1) →
    ∃ L : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, f n) / N) atTop (𝓝 L)

/--
Resolved true: Wirsing proved that every real-valued multiplicative function with `|f| ≤ 1` has a
mean value, and Halász generalized this; erdosproblems.com/239 lists the problem as proved. Source:
T. F. Bloom, Erdős Problems, Problem #239, https://www.erdosproblems.com/239 (status PROVED (LEAN));
resolution: E. Wirsing, Das asymptotische Verhalten von Summen über multiplikative Funktionen. II,
Acta Math. Acad. Sci. Hungar. 18 (1967), 411-467, erdosproblems.com/239: proved by Wirsing [Wi67],
generalized by Halász (1968), https://doi.org/10.1007/BF02280301.
-/
public theorem_wanted multiplicativeSignMeanConverges_holds : multiplicativeSignMeanConverges

end MathlibExt.NumberTheory.MultiplicativeSignMeanValueErdosProblem239Wanted
