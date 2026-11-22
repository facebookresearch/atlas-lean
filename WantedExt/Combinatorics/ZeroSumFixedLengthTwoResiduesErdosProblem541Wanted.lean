/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Zero sums of a single length (Erdős Problem 541)

Erdős Problem 541 (Graham): let `a₁, …, a_p` be residues modulo a prime `p` such that every nonempty
`S ⊆ [p]` with `∑_{i ∈ S} aᵢ ≡ 0` has the same size `r`. Must at most two distinct residues occur
among the `aᵢ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #541, https://www.erdosproblems.com/541 (status PROVED
(LEAN)). UnsolvedMath record UM-30006924 (`EP-541`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for primes as posed; Gao, Hamidoune and Wang proved it for every modulus. Compared with the
formal-conjectures statement `ErdosProblems/541.lean` (equivalent to `erdos_541`; no code imported).
-/

/-- Erdős Problem 541 (Graham): for a prime `p` and residues `a₁, …, a_p` modulo `p` (not
necessarily distinct) such that all nonempty zero-sum index sets `S ⊆ [p]` have one common size
`r`, at most two distinct residues occur among the `aᵢ`. -/
def fixedZeroSumLengthTwoResidues : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : Fin p → ZMod p,
    (∃ r : ℕ, ∀ S : Finset (Fin p), S.Nonempty → ∑ i ∈ S, a i = 0 → S.card = r) →
      (Set.range a).ncard ≤ 2

/--
Resolved true: Erdős and Szemerédi proved it for all large primes `p`, and Gao, Hamidoune and Wang
for every modulus. Source: T. F. Bloom, Erdős Problems, Problem #541,
https://www.erdosproblems.com/541 (status PROVED (LEAN)); resolution: W. Gao, Y. O. Hamidoune and G.
Wang, Distinct length modular zero-sum subsequences: a proof of Graham's conjecture, J. Number
Theory (2010), 1425-1431, erdosproblems.com/541: proved by Erdős and Szemerédi for large p and by
Gao, Hamidoune and Wang for all moduli, https://www.erdosproblems.com/541.
-/
public theorem_wanted fixedZeroSumLengthTwoResidues_holds : fixedZeroSumLengthTwoResidues

end MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541Wanted
