/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large sets avoiding a given subset sum (Erdős Problem 771)

Erdős Problem 771 (Erdős and Graham): let `f(n)` be maximal such that, for every `m ≥ 1`, there
exists `S ⊆ {1, …, n}` with `|S| = f(n)` such that `m ≠ ∑_{a ∈ A} a` for all `A ⊆ S`. Is it true
that `f(n) = (1/2 + o(1)) n / log n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.AvoidedSubsetSumErdosProblem771Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #771, https://www.erdosproblems.com/771 (status
PROVED). UnsolvedMath record UM-30007025 (`EP-771`), dataset ulamai/UnsolvedMath v1.8.0.

As on erdosproblems.com/771, `S` may depend on `m` (Erdős and Graham take `S` the multiples of the
least prime not dividing `m`). The property is downward closed in the size, so `f(n) = (1/2 + o(1))
n / log n` is stated as: for every `ε > 0` and all large `n`, some size `≥ (1/2 - ε) n / log n` has
the property and no size above `(1/2 + ε) n / log n` does (natural logarithm). Compared with the
formal-conjectures statement `ErdosProblems/771.lean` (equivalent; no code imported).
-/

/-- For every `m ≥ 1` some `k`-element `S ⊆ {1, …, n}` has no subset with sum `m` (`S` depends on
`m`). -/
def IsSubsetSumAvoiding (n k : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ S ⊆ Finset.Icc 1 n, S.card = k ∧ ∀ T ⊆ S, ∑ a ∈ T, a ≠ m

/-- Erdős Problem 771 (Erdős and Graham): `f(n) = (1/2 + o(1)) n / log n`, where `f(n)` is the
largest `k` with `IsSubsetSumAvoiding n k`. -/
def subsetSumAvoidingAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (∃ k : ℕ, (1 / 2 - ε) * (n / Real.log n) ≤ k ∧ IsSubsetSumAvoiding n k) ∧
    ∀ k : ℕ, IsSubsetSumAvoiding n k → (k : ℝ) ≤ (1 / 2 + ε) * (n / Real.log n)

/--
Resolved true: Erdős and Graham proved `f(n) ≥ (1/2 + o(1)) n / log n` and Alon and Freiman proved
`f(n) ≤ (1/2 + o(1)) n / log n`; erdosproblems.com/771 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #771, https://www.erdosproblems.com/771 (status PROVED); resolution:
N. Alon and G. Freiman, On sums of subsets of a set of integers, Combinatorica 8 (1988), 297-306
(upper bound); P. Erdős and R. L. Graham (lower bound, as given on erdosproblems.com/771),
Alon-Freiman abstract: for n ≥ n(ε) and m in a range up to n²/(20 log² n), the largest subset of {1,
…, n} with no subset summing to m has ⌊n/s⌋ + s - 2 elements, s the least integer not dividing m, a
special case establishing the conjecture of Erdős and Graham; erdosproblems.com/771: Erdős and
Graham proved f(n) ≥ (1/2 + o(1)) n/log n (S the multiples of the least prime not dividing m), and
Alon and Freiman take m = lcm(1, …, s) with s maximal such that m ≤ n²/(20 (log n)²),
https://web.math.princeton.edu/~nalon/PDFS/Publications/On%20sums%20of%20subsets%20of%20a%20set%20of%20integers.pdf.
-/
public theorem_wanted subsetSumAvoidingAsymptotic_holds : subsetSumAvoidingAsymptotic

end MathlibExt.NumberTheory.AvoidedSubsetSumErdosProblem771Wanted
