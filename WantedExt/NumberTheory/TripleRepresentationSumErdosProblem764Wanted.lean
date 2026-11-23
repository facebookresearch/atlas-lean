/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three-fold Erdős-Fuchs (Erdős Problem 764)

Erdős Problem 764: let `A ⊆ ℕ`. Can there exist a constant `c > 0` such that `∑_{n ≤ N} 1_A ∗ 1_A ∗
1_A (n) = c N + O(1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal

@[expose] public section

namespace MathlibExt.NumberTheory.TripleRepresentationSumErdosProblem764Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #764, https://www.erdosproblems.com/764 (status
DISPROVED). UnsolvedMath record UM-30007022 (`EP-764`), dataset ulamai/UnsolvedMath v1.8.0.

`1_A ∗ 1_A ∗ 1_A (n)` is the number of ordered triples of elements of `A` with sum `n`
(`MathlibExt`'s `AdditiveCombinatorics.orderedRepresentationCount` counts pairs only, so the triple
count is defined here); `A` may contain `0`. `c N + O(1)` is a uniform bound on `|∑_{n ≤ N} 1_A ∗
1_A ∗ 1_A (n) - c N|`. Compared with the formal-conjectures statement `ErdosProblems/764.lean`
(equivalent; no code imported).
-/

open Classical in
/-- `1_A ∗ 1_A ∗ 1_A (n)`: the number of ordered triples of elements of `A` with sum `n`. -/
noncomputable def tripleRepresentations (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple 3 n).filter fun x => ∀ i, x i ∈ A).card

/-- Erdős Problem 764: some `A ⊆ ℕ` and `c > 0` satisfy
`∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A (n) = c N + O(1)`. -/
def tripleRepresentationSumLinear : Prop :=
  ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ,
    |(∑ n ∈ Finset.range (N + 1), (tripleRepresentations A n : ℝ)) - c * N| ≤ C

/--
Resolved false: Vaughan proved that `∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A (n) = c N + o(N^{1/4} (log
N)^{-1/2})` is impossible (his result covers every `h`-fold convolution), so the error cannot be
`O(1)`; erdosproblems.com/764 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems,
Problem #764, https://www.erdosproblems.com/764 (status DISPROVED); resolution: R. C. Vaughan, On
the addition of sequences of integers, J. Number Theory 4 (1972), 1-16; M. Tang, On a generalization
of a theorem of Erdős and Fuchs, Discrete Math. 309 (2009), 6288-6293, erdosproblems.com/764:
Vaughan showed that ∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A(n) = cN + o(N^{1/4} (log N)^{-1/2}) is impossible, his
result covering every h-fold convolution; arXiv:1209.3233, Section 1: Tang proved that for k ≥ 2,
∑_{m ≤ n} r_{k,A}(m) = Cn + o(n^{1/4}) cannot hold for all large n, where r_{k,A}(n) counts the
ordered k-tuples of elements of A with sum n, https://www.erdosproblems.com/764.
-/
public theorem_wanted tripleRepresentationSumLinear_refuted : ¬ tripleRepresentationSumLinear

end MathlibExt.NumberTheory.TripleRepresentationSumErdosProblem764Wanted
