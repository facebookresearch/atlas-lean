/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.NumberTheory.NonSquarefreeBaseTwoPseudoprime

open MathlibExt.NumberTheory.NonSquarefreeBaseTwoPseudoprimeWanted

-- Extract a repeated prime factor and coprimality with the base from the existence theorem.
example : ∃ n p : ℕ, 10 ^ 13 < n ∧ n.Coprime 2 ∧ p.Prime ∧ p ^ 2 ∣ n := by
  obtain ⟨n, hpsp, hnsq, hgt⟩ := conjecture_holds
  obtain ⟨p, hp, hdvd⟩ : ∃ p : ℕ, p.Prime ∧ p * p ∣ n := by
    simpa [Nat.squarefree_iff_prime_squarefree] using hnsq
  exact ⟨n, p, hgt, Nat.coprime_of_fermatPsp hpsp (by decide), hp, by simpa [sq] using hdvd⟩

-- The displayed factorization has a repeated prime even though the witness is not a square.
example : 10063351640161 = 73 * 257 * 449 * 1093 ^ 2 ∧ ¬ IsSquare (10063351640161 : ℕ) := by
  norm_num
