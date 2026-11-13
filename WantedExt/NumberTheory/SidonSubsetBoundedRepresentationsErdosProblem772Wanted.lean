/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sidon subsets of sets with few representations (Erdős Problem 772)

Erdős Problem 772: let `k ≥ 1` and let `H_k(n)` be the maximal `r` such that every `A ⊂ ℕ` with `|A|
= n` and `‖1_A ∗ 1_A‖_∞ ≤ k` contains a Sidon set of size at least `r`. Is it true that `H_k(n) /
n^{1/2} → ∞`? Or even `H_k(n) > n^{1/2 + c}` for some constant `c > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Additive.RepresentationCount
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #772, https://www.erdosproblems.com/772 (status
PROVED). UnsolvedMath record UM-30007026 (`EP-772`), dataset ulamai/UnsolvedMath v1.8.0.

`1_A ∗ 1_A (m)` counts ordered pairs, as a convolution (`MathlibExt`'s
`AdditiveCombinatorics.orderedRepresentationCount`). Sidon is `MathlibExt`'s `Set.IsSidon`. Both
questions are stated without the `sSup` defining `H_k(n)`: `H_k(n) / √n → ∞` is 'for every `C` and
all large `n`, every admissible `A` has a Sidon subset of size `≥ C √n`', and `H_k(n) > n^{1/2 + c}`
is 'for all large `n`, every admissible `A` has a Sidon subset of size `> n^{1/2 + c}`' (the
question is asymptotic; at `n = 1` the strict inequality fails). For `k = 1` no `A` with two or more
elements is admissible, so that case is vacuous. Compared with the formal-conjectures statement
`ErdosProblems/772.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 772, first question: for every `k ≥ 1`, `H_k(n) / √n → ∞`, where
`‖1_A ∗ 1_A‖_∞ ≤ k` bounds `AdditiveCombinatorics.orderedRepresentationCount` (ordered pairs). -/
def sidonSubsetBeyondSqrt : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, A.card = n →
    (∀ m, AdditiveCombinatorics.orderedRepresentationCount (A : Set ℕ) m ≤ k) →
      ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧ C * Real.sqrt n ≤ S.card

/-- Erdős Problem 772, second question: for every `k ≥ 1` some `c > 0` has `H_k(n) > n^{1/2 + c}`
for all large `n`. -/
def sidonSubsetPowerGain : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, A.card = n →
    (∀ m, AdditiveCombinatorics.orderedRepresentationCount (A : Set ℕ) m ≤ k) →
      ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧ (n : ℝ) ^ ((1 : ℝ) / 2 + c) < S.card

/--
Resolved true: Alon and Erdős proved `H_k(n) ≫_k n^{2/3}`, so `H_k(n) / √n → ∞`;
erdosproblems.com/772 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#772, https://www.erdosproblems.com/772 (status PROVED); resolution: N. Alon and P. Erdős, An
application of graph theory to additive number theory, European J. Combin. 6 (1985), 201-203,
Theorem 1: every B_2^{(k)} sequence of n terms (at most k representations of each integer as a sum
of two distinct terms) is a union of C_2(k) n^{1/3} Sidon (B_2) sequences, so it has a Sidon
subsequence of c_4(k) n^{2/3} terms (inequality (4)); a set with ‖1_A ∗ 1_A‖_∞ ≤ k is a B_2^{(k)}
sequence,
https://web.math.princeton.edu/~nalon/PDFS/Publications2/An%20application%20of%20graph%20theory%20to%20additive%20number%20theory.pdf.
-/
public theorem_wanted sidonSubsetBeyondSqrt_holds : sidonSubsetBeyondSqrt

/--
Resolved true: Alon and Erdős proved `H_k(n) ≫_k n^{2/3}`; erdosproblems.com/772 answers both
questions yes. Source: T. F. Bloom, Erdős Problems, Problem #772, https://www.erdosproblems.com/772
(status PROVED); resolution: N. Alon and P. Erdős, An application of graph theory to additive number
theory, European J. Combin. 6 (1985), 201-203, Theorem 1: every B_2^{(k)} sequence of n terms (at
most k representations of each integer as a sum of two distinct terms) is a union of C_2(k) n^{1/3}
Sidon (B_2) sequences, so it has a Sidon subsequence of c_4(k) n^{2/3} terms (inequality (4)); a set
with ‖1_A ∗ 1_A‖_∞ ≤ k is a B_2^{(k)} sequence,
https://web.math.princeton.edu/~nalon/PDFS/Publications2/An%20application%20of%20graph%20theory%20to%20additive%20number%20theory.pdf.
-/
public theorem_wanted sidonSubsetPowerGain_holds : sidonSubsetPowerGain

end MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted
