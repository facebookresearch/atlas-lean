/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.KaprekarMaximalPeriod

/-!
# Long Kaprekar cycles force a prime base

In odd bases `B > 3`, every four-digit Kaprekar cycle has length at most `(B - 1) / 2`,
and equality forces `B` to be prime.
-/

namespace MetaMathlibExt

/-- **Long Kaprekar cycles force a prime base.** Let $B > 3$ be odd, let $K_B$ be the four-digit
Kaprekar map and $X_B$ its state space. Every point of $X_B$ that is periodic for $K_B$ has
minimal period at most $(B - 1)/2$, and if some point of $X_B$ has minimal period exactly
$(B - 1)/2$ under $K_B$, then $B$ is prime.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 22 (`jis-2026-26.4.7-cor-22`). -/
public theorem kaprekar_minimalPeriod_le_and_prime_of_eq (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    (∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
      Function.minimalPeriod (kaprekarFourDigitStep B) d ≤ (B - 1) / 2) ∧
      ((∃ d ∈ kaprekarFourDigitStates B,
          Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) → B.Prime) := by
  obtain ⟨hbound, heq⟩ := kaprekar_minimalPeriod_le_and_eq_iff B hB hB3
  exact ⟨hbound, fun h => (heq.mp h).2.1⟩

end MetaMathlibExt
