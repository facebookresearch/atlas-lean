/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.CardUnitsQuotient
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Ideal UniqueFactorizationMonoid

/-! Tests for `MathlibExt.RingTheory.DedekindDomain.CardUnitsQuotient`. -/

-- The absolute norm of `pℤ` is `p`.
theorem absNorm_span_int (p : ℕ) : absNorm (span {(p : ℤ)}) = p := by
  rw [absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]

-- `#(ℤ/9ℤ)ˣ = 3² - 3 = 6`, from the prime-power count with `𝔭 = 3ℤ` and `k = 2`.
example : Nat.card (ℤ ⧸ span {((3 : ℕ) : ℤ)} ^ 2)ˣ = 6 := by
  have : (span {((3 : ℕ) : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Nat.prime_iff_prime_int.mp Nat.prime_three)
  rw [natCard_units_quotient_pow (by simp) two_ne_zero, absNorm_span_int]
  norm_num

-- `#(ℤ/5ℤ)ˣ = 5 · (1 - 1/5) = 4`, from the product formula for the prime ideal `5ℤ`.
example : (Nat.card (ℤ ⧸ span {((5 : ℕ) : ℤ)})ˣ : ℚ) = 4 := by
  have hne : span {((5 : ℕ) : ℤ)} ≠ ⊥ := by simp
  have hprime : (span {((5 : ℕ) : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Nat.prime_iff_prime_int.mp Nat.prime_five)
  have hfac : normalizedFactors (span {((5 : ℕ) : ℤ)}) = {span {((5 : ℕ) : ℤ)}} := by
    rw [normalizedFactors_irreducible (prime_of_isPrime hne hprime).irreducible, normalize_eq]
  rw [natCard_units_quotient hne, hfac, Multiset.toFinset_singleton, Finset.prod_singleton,
    absNorm_span_int]
  norm_num

-- The prime-power count applies to the ring of integers of any number field.
example (K : Type*) [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K))
    [P.IsPrime] (hP : P ≠ ⊥) :
    Nat.card (NumberField.RingOfIntegers K ⧸ P ^ 3)ˣ = absNorm P ^ 3 - absNorm P ^ 2 :=
  natCard_units_quotient_pow hP (by norm_num)

-- So does the product formula.
example (K : Type*) [Field K] [NumberField K] (I : Ideal (NumberField.RingOfIntegers K))
    (hI : I ≠ ⊥) :
    (Nat.card (NumberField.RingOfIntegers K ⧸ I)ˣ : ℚ) =
      absNorm I * ∏ P ∈ (normalizedFactors I).toFinset, (1 - 1 / (absNorm P : ℚ)) :=
  natCard_units_quotient hI

end
