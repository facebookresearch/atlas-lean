/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Exact additive complements (Erdős Problem 785)

Erdős Problem 785 (Erdős and Danzer): let `A, B ⊆ ℕ` be infinite sets such that `A + B` contains all
large integers, and let `A(x) = |A ∩ [1, x]|`, `B(x) = |B ∩ [1, x]|`. If `A(x) B(x) ∼ x`, is it true
that `A(x) B(x) - x → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ExactAdditiveComplementsErdosProblem785Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #785, https://www.erdosproblems.com/785 (status PROVED
(LEAN)). UnsolvedMath record UM-30007033 (`EP-785`), dataset ulamai/UnsolvedMath v1.8.0.

`A` and `B` are sets of positive integers (`0 ∉ A`, `0 ∉ B`, matching the counting functions on `[1,
x]`); 'all large integers' is `∀ᶠ m, m ∈ A + B`. Such pairs exist (Danzer). Compared with the
formal-conjectures statement `ErdosProblems/785.lean` (equivalent; no code imported).
-/

open Classical in
/-- The counting function `A(x) = |A ∩ [1, x]|`. -/
noncomputable def countingFunction (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (· ∈ A)).card

/-- Erdős Problem 785 (Erdős and Danzer): if `A, B` are infinite sets of positive integers, `A + B`
contains all large integers and `A(x) B(x) ∼ x`, then `A(x) B(x) - x → ∞`. -/
def exactComplementsExcessDiverges : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → 0 ∉ A → 0 ∉ B →
    (∀ᶠ m : ℕ in Filter.atTop, ∃ a ∈ A, ∃ b ∈ B, a + b = m) →
    Filter.Tendsto (fun x : ℕ => (countingFunction A x * countingFunction B x : ℝ) / x)
      Filter.atTop (nhds 1) →
    Filter.Tendsto (fun x : ℕ => (countingFunction A x * countingFunction B x : ℝ) - x)
      Filter.atTop Filter.atTop

/--
Resolved true: Sárközy and Szemerédi proved that additive complements with `lim sup A(x) B(x) / x ≤
1`, in particular exact ones, have `A(x) B(x) - x → ∞` (as quoted by Fang and Chen);
erdosproblems.com/785 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#785, https://www.erdosproblems.com/785 (status PROVED (LEAN)); resolution: A. Sárközy and E.
Szemerédi, On a problem in additive number theory, Acta Math. Hungar. (1994), 237-245; J.-H. Fang
and Y.-G. Chen, On additive complements, Proc. Amer. Math. Soc. 138 (2010), 1923-1927, Fang-Chen
abstract: for additive complements A, B (infinite sequences of non-negative integers whose sumset
contains all large integers), Sárközy and Szemerédi proved that lim sup A(x)B(x)/x ≤ 1 implies
A(x)B(x) - x → +∞; erdosproblems.com/785: the answer is yes, proved by Sárközy and Szemerédi,
https://doi.org/10.1090/S0002-9939-10-10205-6.
-/
public theorem_wanted exactComplementsExcessDiverges_holds : exactComplementsExcessDiverges

end MathlibExt.NumberTheory.ExactAdditiveComplementsErdosProblem785Wanted
