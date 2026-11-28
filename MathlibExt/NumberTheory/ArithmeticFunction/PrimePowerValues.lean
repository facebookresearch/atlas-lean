/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Arithmetic functions from prime-power values

For a commutative monoid with zero `R`, a family of values `a p e : R` at prime powers `p ^ e`
with `e ≠ 0` extends to a multiplicative arithmetic function by taking the product over the prime
factorization. The value at `1` is the empty product; the coefficients `a p 0` are not used.

## References

* The construction and prime-power evaluation are adapted from `ofLocal`,
  `ofLocal_multiplicative`, and `ofLocal_prime_pow` in
  [`MathlibExt.NumberTheory.KFullPowerFreeParity` at their original location](https://github.com/facebookresearch/atlas-lean/blob/9ab9827017c4c4046fb6582bd187818d74f4da8f/MathlibExt/NumberTheory/KFullPowerFreeParity.lean#L233-L252).
* `MetaMathlibExt.multiplicativeOfPrimePowers` in
  `MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution` treats the special case in
  which the coefficients depend only on the exponent.
-/

namespace ArithmeticFunction

variable {R : Type*} [CommMonoidWithZero R]

/-- Extend coefficients on positive powers of primes to an arithmetic function by taking their
product over the prime factorization of a nonzero natural number, and assigning `0` to `0`. -/
@[expose] public def ofPrimePowerValues (a : ℕ → ℕ → R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod a, by simp⟩

/-- At a nonzero natural number, the extension is the product of the prescribed coefficients
at its prime-power factors. -/
public theorem ofPrimePowerValues_apply_of_ne_zero (a : ℕ → ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    ofPrimePowerValues a n = n.factorization.prod a := by
  change (if n = 0 then 0 else n.factorization.prod a) = _
  rw [ite_eq_right hn]

/-- The extension of prescribed prime-power values is multiplicative, since coprime positive
integers have disjoint sets of prime factors. -/
public theorem isMultiplicative_ofPrimePowerValues (a : ℕ → ℕ → R) :
    (ofPrimePowerValues a).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [ofPrimePowerValues], fun {m n} hm hn hmn => ?_⟩
  rw [ofPrimePowerValues_apply_of_ne_zero a (mul_ne_zero hm hn),
    ofPrimePowerValues_apply_of_ne_zero a hm, ofPrimePowerValues_apply_of_ne_zero a hn,
    Nat.factorization_mul_of_coprime hmn]
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors a

/-- The extension takes its prescribed value at `p ^ e` for prime `p` and nonzero `e`. -/
public theorem ofPrimePowerValues_prime_pow (a : ℕ → ℕ → R) {p e : ℕ}
    (hp : p.Prime) (he : e ≠ 0) : ofPrimePowerValues a (p ^ e) = a p e := by
  rw [ofPrimePowerValues_apply_of_ne_zero a (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
    hp.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.prod,
    Finsupp.support_single _ he, Finset.prod_singleton, Finsupp.single_eq_same]

end ArithmeticFunction
