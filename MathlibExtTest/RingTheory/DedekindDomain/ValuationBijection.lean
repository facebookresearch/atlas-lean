/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.ValuationBijection
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Ideal.Maximal

@[expose] public section

/-!
# Tests for Theorem 8.20

All tests use the trivial AKLB extension `A = B = ℤ`, `K = L = ℚ`, where
the integral-closure and fraction-ring instances are found automatically.
The prime `(2)` of `ℤ` is the only prime above itself, and its `2`-adic
valuation is the only valuation extending itself, so the bijection of
Theorem 8.20 is exercised at a concrete, non-vacuous instance.
-/

namespace ValuationBijectionTest

open ValuationBijection
open IsDedekindDomain

/-- The prime `(2)` of `ℤ`, as a height-one prime. -/
noncomputable def primeTwoSpec : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(2 : ℤ)}
  isPrime := by
    rw [Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)]
    exact Int.prime_two
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num

/-- In the identity extension, `(2)` lies over itself. -/
theorem primeTwo_liesOver_self :
    primeTwoSpec.asIdeal.LiesOver primeTwoSpec.asIdeal := ⟨rfl⟩

/-- `(2)` is the prime above `(2)` in the identity extension. -/
theorem primeTwo_mem_primesAbove :
    primeTwoSpec ∈ primesAbove ℤ ℤ primeTwoSpec := ⟨rfl⟩

/-- The `2`-adic valuation extends the `2`-adic valuation. -/
theorem primeTwo_valuation_extends :
    extendsValuation ℤ ℚ ℚ primeTwoSpec (primeTwoSpec.valuation ℚ) :=
  valuation_extends_of_liesOver ℤ ℚ ℚ ℤ primeTwoSpec primeTwoSpec ⟨rfl⟩

/-- The `2`-adic valuation is equivalent to itself via
`dvr_overring_equiv`: its unit ball is exactly `(2)`. -/
theorem primeTwo_dvr_overring_equiv :
    (primeTwoSpec.valuation ℚ).IsEquiv (primeTwoSpec.valuation ℚ) :=
  dvr_overring_equiv primeTwoSpec (primeTwoSpec.valuation ℚ)
    (fun b => HeightOneSpectrum.valuation_le_one primeTwoSpec b)
    (fun b => (HeightOneSpectrum.valuation_lt_one_iff_mem primeTwoSpec b).symm)

/-- Surjectivity of Theorem 8.20 at `(2)`: the `2`-adic valuation comes
from a prime above `(2)`. -/
theorem primeTwo_surjectivity :
    ∃ 𝔮 : HeightOneSpectrum ℤ,
      𝔮 ∈ primesAbove ℤ ℤ primeTwoSpec ∧
        (𝔮.valuation ℚ).IsEquiv (primeTwoSpec.valuation ℚ) :=
  (extending_valuation_bijection_primes_above ℤ ℚ ℚ ℤ primeTwoSpec).2
    (primeTwoSpec.valuation ℚ) primeTwo_valuation_extends

/-- Injectivity of Theorem 8.20 at `(2)`: a prime above `(2)` whose
valuation is equivalent to the `2`-adic valuation is `(2)` itself. -/
theorem primeTwo_injectivity (𝔮 : HeightOneSpectrum ℤ)
    (h𝔮 : 𝔮 ∈ primesAbove ℤ ℤ primeTwoSpec)
    (hequiv : (𝔮.valuation ℚ).IsEquiv (primeTwoSpec.valuation ℚ)) :
    𝔮 = primeTwoSpec :=
  (extending_valuation_bijection_primes_above ℤ ℚ ℚ ℤ primeTwoSpec).1
    𝔮 primeTwoSpec h𝔮 ⟨rfl⟩ hequiv

#print axioms ValuationBijection.valuation_extends_of_liesOver
#print axioms ValuationBijection.dvr_overring_equiv
#print axioms ValuationBijection.extending_valuation_bijection_primes_above

end ValuationBijectionTest

end
