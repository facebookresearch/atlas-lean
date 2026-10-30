/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Zero subset sums in `ℤ / N ℤ` (Erdős Problem 540)

Erdős Problem 540 (Erdős and Heilbronn): if `A ⊆ ℤ / N ℤ` has size `≫ N ^ (1/2)`, is there a
nonempty `S ⊆ A` with `∑_{n ∈ S} n ≡ 0 (mod N)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #540, https://www.erdosproblems.com/540 (status PROVED
(LEAN)). UnsolvedMath record UM-30006923 (`EP-540`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ N ^ (1/2)` is `|A| ≥ C √N` for one absolute `C`. Compared with the formal-conjectures statement
`ErdosProblems/540.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 540 (Erdős and Heilbronn): there is `C > 0` such that for every `N ≥ 1`, every
`A ⊆ ℤ / N ℤ` with `|A| ≥ C √N` has a nonempty subset with sum `0`. -/
def sqrtSizeHasZeroSubsetSum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ A : Finset (ZMod N), C * Real.sqrt N ≤ A.card →
    ∃ S ⊆ A, S.Nonempty ∧ ∑ x ∈ S, x = 0

/--
Resolved true: Olson proved it for prime `N` and Szemerédi for all `N` (in every finite abelian
group); Hamidoune and Zémor showed `(1 + o(1)) √(2N)` suffices. Source: T. F. Bloom, Erdős Problems,
Problem #540, https://www.erdosproblems.com/540 (status PROVED (LEAN)); resolution: E. Szemerédi, On
a conjecture of Erdős and Heilbronn, Acta Arith. (1970), 227-229, erdosproblems.com/540: yes; Olson
for N prime, Szemerédi for all N (indeed for all finite abelian groups),
https://www.erdosproblems.com/540.
-/
public theorem_wanted sqrtSizeHasZeroSubsetSum_holds : sqrtSizeHasZeroSubsetSum

end MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted
