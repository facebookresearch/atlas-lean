/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectExistsPrimeGeFiveDvdSigmaBiunitaryPrimePow

/-!
# Tests for prime factors of biunitary divisor sums of prime powers

Concrete instances and corollaries of
`MetaMathlibExt.exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow`.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction
namespace BiunitaryTriperfectExistsPrimeGeFiveDvdSigmaBiunitaryPrimePow

open MetaMathlibExt

-- At `(p, g) = (2, 2)` the sum is `5`, so the witness is forced to be `5`.
example (q : ℕ) (hq : q.Prime) (hdvd : q ∣ sigmaBiunitary (2 ^ 2)) (h5 : 5 ≤ q) :
    q = 5 := by
  have h : sigmaBiunitary (2 ^ 2) = 5 := by decide
  rw [h] at hdvd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with h1 | rfl
  · have h2 := hq.two_le
    omega
  · rfl

-- At `(p, g) = (3, 2)` the sum is `10`, witnessed by `5`.
example : 5 ∣ sigmaBiunitary (3 ^ 2) := by decide

-- At `(p, g) = (2, 5)` the sum is `63`, witnessed by `7`.
example : 7 ∣ sigmaBiunitary (2 ^ 5) := by decide

-- The witness lies outside `{2, 3}`.
example (p g : ℕ) (hp : p.Prime) (hg : 2 ≤ g) (hexc : ¬ (p = 2 ∧ g = 4)) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ q ∉ ({2, 3} : Finset ℕ) := by
  obtain ⟨q, hq, hdvd, h5⟩ :=
    exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow p g hp hg hexc
  exact ⟨q, hq, hdvd, by simp; omega⟩

end BiunitaryTriperfectExistsPrimeGeFiveDvdSigmaBiunitaryPrimePow
end MathlibExtTest.NumberTheory.ArithmeticFunction
