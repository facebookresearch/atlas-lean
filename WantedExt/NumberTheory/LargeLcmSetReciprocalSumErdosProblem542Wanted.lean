/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets with pairwise large least common multiples (Erdős Problem 542)

Erdős Problem 542: if `A ⊆ {1, …, n}` has `lcm(a, b) > n` for all distinct `a, b ∈ A`, is `∑_{a ∈ A}
1/a ≤ 31/30`? Must `≫ n` integers `m ≤ n` avoid the elements of `A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.LargeLcmSetReciprocalSumErdosProblem542Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #542, https://www.erdosproblems.com/542 (status
SOLVED). UnsolvedMath record UM-30006925 (`EP-542`), dataset ulamai/UnsolvedMath v1.8.0.

In the second question the page says "do not divide any `a ∈ A`", which is trivially false (`A =
(n/2, n]`); the intended and resolved reading is "divisible by no `a ∈ A`" (the multiples of
distinct elements are disjoint). `A = {1}` is excluded there, as it leaves no such `m`. The claim is
read for large `n`, so its refutation is the stronger statement. Compared with the
formal-conjectures statement `ErdosProblems/542.lean` (the same readings; no code imported).
-/

/-- `A ⊆ {1, …, n}` and `lcm(a, b) > n` for all distinct `a, b ∈ A`. -/
def IsLargeLcmSet (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

/-- Erdős Problem 542, first question: every such `A` has `∑_{a ∈ A} 1/a ≤ 31/30`. -/
def largeLcmReciprocalSumBound : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), IsLargeLcmSet n A → ∑ a ∈ A, (1 : ℝ) / a ≤ 31 / 30

/-- Erdős Problem 542, second question: there is `c > 0` such that for all large `n` and every
such `A` with `1 ∉ A`, at least `c n` integers `m ≤ n` are divisible by no element of `A`. -/
def largeLcmUncoveredLinear : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset ℕ, IsLargeLcmSet n A → 1 ∉ A →
    c * n ≤ (((Finset.Icc 1 n).filter fun m => ∀ a ∈ A, ¬ a ∣ m).card : ℝ)

/--
Resolved true: Schinzel and Szekeres proved `∑_{a ∈ A} 1/a ≤ 31/30`, attained by `{2, 3, 5}`.
Source: T. F. Bloom, Erdős Problems, Problem #542, https://www.erdosproblems.com/542 (status
SOLVED); resolution: A. Schinzel and G. Szekeres, Sur un problème de M. Paul Erdős, Acta Sci. Math.
(Szeged) (1959), 221-229, erdosproblems.com/542: first question yes, second no, with examples
leaving at most n/(log n)^c such m, https://www.erdosproblems.com/542.
-/
public theorem_wanted largeLcmReciprocalSumBound_holds : largeLcmReciprocalSumBound

/--
Resolved false: Schinzel and Szekeres constructed such `A` (with `1 ∉ A`) leaving at most `n / (log
n) ^ c` integers `m ≤ n` divisible by no element of `A`, for some `c > 0`. Source: T. F. Bloom,
Erdős Problems, Problem #542, https://www.erdosproblems.com/542 (status SOLVED); resolution: A.
Schinzel and G. Szekeres, Sur un problème de M. Paul Erdős, Acta Sci. Math. (Szeged) (1959),
221-229, erdosproblems.com/542: first question yes, second no, with examples leaving at most n/(log
n)^c such m, https://www.erdosproblems.com/542.
-/
public theorem_wanted largeLcmUncoveredLinear_refuted : ¬ largeLcmUncoveredLinear

end MathlibExt.NumberTheory.LargeLcmSetReciprocalSumErdosProblem542Wanted
