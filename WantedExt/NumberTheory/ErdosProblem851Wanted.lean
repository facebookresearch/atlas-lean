/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.Data.Set.Density
public import Batteries.Util.ProofWanted

@[expose] public section

/-!
# Erdős Problem #851

Romanoff's theorem gives positive lower density for the integers of the form
`2 ^ k + p` with `p` prime. Moreover, for every `ε > 0` there is `r` such that
the integers of the form `2 ^ k + n` with `n` having at most `r` distinct prime
divisors have lower density at least `1 - ε`.
-/

namespace MathlibExt.NumberTheory.ErdosProblem851Wanted

/-- At most `r` distinct prime divisors for `n : ℕ` (source EP-851 [Erdős Problems]). -/
def HasAtMostRPrimeFactors (n r : ℕ) : Prop :=
  n.primeFactors.card ≤ r

/-- Representability as `2 ^ k + n` with `k ≥ 0` and `n` having at most `r`
prime divisors (source EP-851 [Erdős Problems]). -/
def Representable (r m : ℕ) : Prop :=
  ∃ k n : ℕ, m = 2 ^ k + n ∧ HasAtMostRPrimeFactors n r

/-- Representability as `2 ^ k + p` with `p` prime (Romanoff's theorem in
EP-851 [Erdős Problems]). -/
def PrimeRepresentable (m : ℕ) : Prop :=
  ∃ k p : ℕ, m = 2 ^ k + p ∧ p.Prime

/-- Erdős Problem #851: Romanoff's positive-density theorem together with the
resolved question that, for every `ε > 0`, some bound `r` makes the integers
`2 ^ k + n` with at most `r` distinct prime divisors have lower density at
least `1 - ε` (source EP-851 [Erdős Problems]). -/
noncomputable def Statement : Prop :=
  0 < Set.lowerDensity {m | PrimeRepresentable m} ∧
    ∀ (ε : ℝ), ε > 0 → ∃ r : ℕ, 1 - ε ≤ Set.lowerDensity {m | Representable r m}

/--
Resolved true: Romanoff proved the positive-density clause in 1934; Price and GPT-5.2 Pro proved
the near-one density statement affirmatively in 2026. Source: Lean proof of Erdős Problem 851,
pinned revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos851.lean#L37;
Yuchen Ding and Wenguang Zhai, A generalization of the Romanoff theorem, arXiv:2401.15892v3
(2024), https://arxiv.org/abs/2401.15892v3. Moved from
`OpenConjectures/NumberTheory/ErdosProblem851`.
-/
public theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.ErdosProblem851Wanted
