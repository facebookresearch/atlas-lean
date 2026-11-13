/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completeness of `{a^k b^l}` (Erdős Problem 246)

Erdős Problem 246: let `(a, b) = 1`. The set `{a^k b^l : k, l ≥ 0}` is complete: every large integer
is a sum of distinct integers of this form.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.CoprimePowerProductsCompleteErdosProblem246Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #246, https://www.erdosproblems.com/246 (status PROVED
(LEAN)). UnsolvedMath record UM-30006791 (`EP-246`), dataset ulamai/UnsolvedMath v1.8.0.

The statement assumes `a, b ≥ 2`, implicit in the source: for `a = 1` and `b = 3` the sums of
distinct powers of `3` miss every integer with a digit `2` in base `3`. Compared with the
formal-conjectures statement `ErdosProblems/246.lean` (equivalent; no code imported).
-/

open Filter

/-- Erdős Problem 246: for coprime `a, b ≥ 2`, every sufficiently large integer is a sum of
distinct integers of the form `a^k b^l` with `k, l ≥ 0`. -/
def coprimePowerProductsComplete : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → Nat.Coprime a b →
    ∀ᶠ n : ℕ in atTop, ∃ S : Finset ℕ, (∀ s ∈ S, ∃ k l : ℕ, s = a ^ k * b ^ l) ∧ ∑ s ∈ S, s = n

/--
Resolved true: Birch proved that for coprime `a, b > 1` every sufficiently large integer is a sum of
distinct numbers `a^k b^l`; erdosproblems.com/246 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #246, https://www.erdosproblems.com/246 (status PROVED (LEAN)); resolution:
B. J. Birch, Note on a problem of Erdős, Proc. Cambridge Philos. Soc. 55 (1959), 370-373,
erdosproblems.com/246: proved by Birch [Bi59]; also a consequence of Cassels (1960),
https://doi.org/10.1017/S0305004100034150.
-/
public theorem_wanted coprimePowerProductsComplete_holds : coprimePowerProductsComplete

end MathlibExt.NumberTheory.CoprimePowerProductsCompleteErdosProblem246Wanted
