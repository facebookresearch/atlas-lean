/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graham's greatest common divisor problem (Erdős Problem 402)

Erdős Problem 402: prove that for every finite set `A ⊆ ℕ` there are `a, b ∈ A` with `gcd(a, b) ≤ a
/ |A|`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.NumberTheory.GrahamGcdProblemErdosProblem402Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #402, https://www.erdosproblems.com/402 (status
PROVED). UnsolvedMath record UM-30006856 (`EP-402`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is nonempty and consists of positive integers (`0 ∈ A` would make `a = b = 0` a trivial
witness). `a = b` is allowed, which matters only for `|A| = 1`. The inequality is written `gcd(a, b)
· |A| ≤ a`. Compared with the formal-conjectures statement `ErdosProblems/402.lean` (equivalent; no
code imported).
-/

/-- Erdős Problem 402 (Graham's conjecture): every nonempty finite set `A` of positive integers
contains `a, b` with `gcd(a, b) ≤ a / |A|`. -/
def existsPairWithSmallGcd : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A → ∃ a ∈ A, ∃ b ∈ A, Nat.gcd a b * A.card ≤ a

/--
Resolved true: Balasubramanian and Soundararajan proved Graham's conjecture for all sets, after
Szegedy and Zaharescu had proved it for all sufficiently large sets; erdosproblems.com/402 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #402,
https://www.erdosproblems.com/402 (status PROVED); resolution: R. Balasubramanian and K.
Soundararajan, On a conjecture of R. L. Graham, Acta Arith. (1996), 1-38, erdosproblems.com/402:
proved for all sets by Balasubramanian and Soundararajan.
-/
public theorem_wanted existsPairWithSmallGcd_holds : existsPairWithSmallGcd

end MathlibExt.NumberTheory.GrahamGcdProblemErdosProblem402Wanted
