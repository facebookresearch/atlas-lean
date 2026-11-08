/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős-Straus representations and the structure of primes

Statement from Marc Chamberland, "The Erdős-Straus Conjecture and the
Structure of Primes", *INTEGERS* 26 (2026), Article A42
(<https://math.colgate.edu/~integers/aa42/aa42.pdf>).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosStrausPrimeStructureWanted

/-- Chamberland's Theorem 1: for a prime `p`, a restricted
Erdős-Straus representation with `p ∤ a` and `p` dividing both `b` and
`c` exists if and only if `p = q * r - 4 * s₁ * s₂` for positive
`q r s₁ s₂` with `q ≡ 3 [MOD 4]` and both `s₁` and `s₂` dividing
`(q + 1) / 4`.

The equality on the right is written as
`p + 4 * s₁ * s₂ = q * r` over `ℕ` to avoid truncated subtraction.

Source: Marc Chamberland, "The Erdős-Straus Conjecture and the
Structure of Primes", Theorem 1. -/
theorem_wanted erdos_straus_prime_restricted_representation_iff
    (p : ℕ) (hp : p.Prime) :
    (∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≤ b ∧ b ≤ c ∧
      ¬p ∣ a ∧ p ∣ b ∧ p ∣ c ∧
      (4 : ℚ) / p = 1 / a + 1 / b + 1 / c) ↔
    (∃ q r s₁ s₂ : ℕ, 0 < q ∧ 0 < r ∧ 0 < s₁ ∧ 0 < s₂ ∧
      q % 4 = 3 ∧ s₁ ∣ (q + 1) / 4 ∧ s₂ ∣ (q + 1) / 4 ∧
      p + 4 * s₁ * s₂ = q * r)

end MathlibExt.NumberTheory.ErdosStrausPrimeStructureWanted
