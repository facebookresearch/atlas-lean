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

/-- **Graham's zero-sum statement (Erdős Problem 541).** This is the statement that for every
prime $p$ and every sequence $a_0, \dots, a_{p-1}$ of residues modulo $p$, not necessarily
distinct, if there is a natural number $r$ such that every nonempty set
$S \subseteq \{0, \dots, p-1\}$ with $\sum_{i \in S} a_i = 0$ in $\mathbb{Z}/p\mathbb{Z}$ has
exactly $r$ elements, then at most two distinct residues occur among $a_0, \dots, a_{p-1}$. -/
def fixedZeroSumLengthTwoResidues : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : Fin p → ZMod p,
    (∃ r : ℕ, ∀ S : Finset (Fin p), S.Nonempty → ∑ i ∈ S, a i = 0 → S.card = r) →
      (Set.range a).ncard ≤ 2

/--
**Zero sums of a single length use at most two residues (Erdős Problem 541).** For every prime
$p$ and every sequence $a_0, \dots, a_{p-1}$ of residues modulo $p$, not necessarily distinct, if
there is a natural number $r$ such that every nonempty set $S \subseteq \{0, \dots, p-1\}$ with
$\sum_{i \in S} a_i = 0$ in $\mathbb{Z}/p\mathbb{Z}$ has exactly $r$ elements, then at most two
distinct residues occur among $a_0, \dots, a_{p-1}$.

Resolved true: Erdős and Szemerédi proved it for all large primes $p$, and Gao, Hamidoune and Wang
for every modulus.

Source: T. F. Bloom, Erdős Problems, Problem #541,
https://www.erdosproblems.com/541 (status PROVED (LEAN)); resolution: W. Gao, Y. O. Hamidoune and G.
Wang, Distinct length modular zero-sum subsequences: a proof of Graham's conjecture, J. Number
Theory (2010), 1425-1431, erdosproblems.com/541: proved by Erdős and Szemerédi for large p and by
Gao, Hamidoune and Wang for all moduli, https://www.erdosproblems.com/541.
-/
public theorem_wanted fixedZeroSumLengthTwoResidues_holds : fixedZeroSumLengthTwoResidues

end MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541Wanted
