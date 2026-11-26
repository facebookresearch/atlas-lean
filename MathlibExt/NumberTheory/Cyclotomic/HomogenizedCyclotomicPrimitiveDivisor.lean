/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Int
public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicProduct
public import MathlibExt.NumberTheory.PrimitiveDivisor

/-!
# Primitive prime divisors and homogenized cyclotomic values

A primitive prime divisor of a difference of powers divides the homogenized
cyclotomic factor at the same index.
-/

namespace MetaMathlibExt

-- Retain the source hypotheses on `a` and `b`; the product argument does not need them.
set_option linter.unusedVariables false in
/-- **Zsigmondy primes divide the homogenized cyclotomic value.** Let $a$ and $b$ be distinct
coprime positive integers and let $n \ge 2$. If $p$ is a primitive prime divisor of the term
$a^n - b^n$ of the integer sequence $(a^m - b^m)_{m \ge 0}$ (a Zsigmondy prime for $(a, b, n)$),
then $p$ divides the homogenized cyclotomic value $\Phi_n(a, b)$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 5. -/
public theorem dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor {a b n p : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p) :
    (p : ℤ) ∣ homogenizedCyclotomic n a b := by
  have hn' : 0 < n := Nat.zero_lt_two.trans_le hn
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.prime
  have hprod := hp.dvd
  rw [← prod_divisors_homogenizedCyclotomic hn' a b] at hprod
  obtain ⟨d, hd, hpd⟩ := hp'.exists_mem_finset_dvd hprod
  have hdpos := Nat.pos_of_mem_divisors hd
  have hpow : (p : ℤ) ∣ (a : ℤ) ^ d - (b : ℤ) ^ d := by
    rw [← prod_divisors_homogenizedCyclotomic hdpos a b]
    exact hpd.trans (Finset.dvd_prod_of_mem _ (d.mem_divisors_self hdpos.ne'))
  have hdn : d = n := le_antisymm (Nat.le_of_dvd hn' (Nat.dvd_of_mem_divisors hd))
    (hp.toIsPrimitiveDivisor.le_of_dvd hdpos hpow)
  simpa only [hdn] using hpd

end MetaMathlibExt
