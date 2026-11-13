/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Reciprocal sums of sets with distinct subset sums (Erdős Problem 350)

Erdős Problem 350: if `A ⊆ ℕ` is a finite set all of whose subset sums are distinct, is `∑_{n ∈ A}
1/n < 2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctSubsetSumsReciprocalErdosProblem350Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #350, https://www.erdosproblems.com/350 (status PROVED
(LEAN)). UnsolvedMath record UM-30006833 (`EP-350`), dataset ulamai/UnsolvedMath v1.8.0.

Distinct subset sums means that distinct subsets `X ≠ Y` of `A` have distinct sums; this forces `0 ∉
A` (the subsets `∅` and `{0}` have equal sums), so `A` consists of positive integers. Compared with
the formal-conjectures statement `ErdosProblems/350.lean` (equivalent; no code imported).
-/

/-- All subsets of `A` have distinct sums. -/
def HasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → ∑ n ∈ X, n ≠ ∑ n ∈ Y, n

/-- Erdős Problem 350: if all subset sums of a finite set `A ⊆ ℕ` are distinct, then
`∑_{n ∈ A} 1/n < 2`. -/
def reciprocalSumLtTwoOfDistinctSubsetSums : Prop :=
  ∀ A : Finset ℕ, HasDistinctSubsetSums A → ∑ n ∈ A, (1 : ℝ) / n < 2

/--
Resolved true: Ryavec proved (the proof is reproduced by Benkoski and Erdős) that such `A` has `∑_{n
∈ A} 1/n ≤ 2 - 2^{1 - |A|} < 2`, with equality only for `A = {1, 2, …, 2^k}`; erdosproblems.com/350
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #350,
https://www.erdosproblems.com/350 (status PROVED (LEAN)); resolution: S. J. Benkoski and P. Erdős,
On weird and pseudoperfect numbers, Math. Comp. (1974), 617-623, reproducing Ryavec's unpublished
proof; formal proof plby/lean-proofs, src/v4.24.0/ErdosProblems/Erdos350.lean, Ryavec: ∑_{n ∈ A} 1/n
≤ 2 - 2^{1-|A|} (erdosproblems.com/350),
https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos350.lean.
-/
public theorem_wanted reciprocalSumLtTwoOfDistinctSubsetSums_holds :
    reciprocalSumLtTwoOfDistinctSubsetSums

end MathlibExt.NumberTheory.DistinctSubsetSumsReciprocalErdosProblem350Wanted
