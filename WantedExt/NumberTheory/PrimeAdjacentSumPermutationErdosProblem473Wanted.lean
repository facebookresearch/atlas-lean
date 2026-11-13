/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutations of the positive integers with prime adjacent sums (Erdős Problem 473)

Erdős Problem 473 (Segal): is there a permutation `a₁, a₂, …` of the positive integers such that
`aₖ + aₖ₊₁` is always prime?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Notation

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeAdjacentSumPermutationErdosProblem473Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #473, https://www.erdosproblems.com/473 (status
PROVED). UnsolvedMath record UM-30006887 (`EP-473`), dataset ulamai/UnsolvedMath v1.8.0.

The permutation is an equivalence `ℕ ≃ ℕ+` (indices shifted to start at `0`). The finite version
(permutations of `{1, …, n}`) and Watts's greedy-sequence question appear in the page commentary,
not in the recorded problem. Compared with the formal-conjectures statement `ErdosProblems/473.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 473: there is a permutation `a 0, a 1, …` of the positive integers with
`a k + a (k + 1)` prime for every `k`. -/
def primeAdjacentSumPermutation : Prop :=
  ∃ a : ℕ ≃ ℕ+, ∀ k : ℕ, ((a k : ℕ) + (a (k + 1) : ℕ)).Prime

/--
Resolved true: erdosproblems.com/473 records the answer yes, as shown by Odlyzko. The identical
formal-conjectures statement `erdos_473` links a Lean proof in plby/lean-proofs (not checked here).
Source: T. F. Bloom, Erdős Problems, Problem #473, https://www.erdosproblems.com/473 (status
PROVED); resolution: A. M. Odlyzko, as recorded on erdosproblems.com/473 (no reference given),
erdosproblems.com/473: the answer is yes, as shown by Odlyzko, https://www.erdosproblems.com/473.
-/
public theorem_wanted primeAdjacentSumPermutation_holds : primeAdjacentSumPermutation

end MathlibExt.NumberTheory.PrimeAdjacentSumPermutationErdosProblem473Wanted
