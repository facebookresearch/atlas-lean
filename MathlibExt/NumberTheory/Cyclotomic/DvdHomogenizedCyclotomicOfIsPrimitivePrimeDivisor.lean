/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicProduct
public import MathlibExt.NumberTheory.PrimitiveDivisor

/-!
# Zsigmondy primes divide homogenized cyclotomic values

A primitive prime divisor of $a^n - b^n$ divides the homogenized cyclotomic value
$\Phi_n(a, b)$.
-/

namespace MetaMathlibExt

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
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.prime
  have hprod : (p : ℤ) ∣ ∏ d ∈ n.divisors, homogenizedCyclotomic d (a : ℤ) (b : ℤ) := by
    rw [prod_divisors_homogenizedCyclotomic (by omega : 0 < n)]
    exact hp.dvd
  obtain ⟨d, hd, hpd⟩ := hprime.exists_mem_finset_dvd hprod
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hdvd : (p : ℤ) ∣ (a : ℤ) ^ d - (b : ℤ) ^ d := by
    have hfac : homogenizedCyclotomic d (a : ℤ) (b : ℤ) ∣ (a : ℤ) ^ d - (b : ℤ) ^ d := by
      rw [← prod_divisors_homogenizedCyclotomic hdpos (a : ℤ) (b : ℤ)]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self d hdpos.ne')
    exact hpd.trans hfac
  have hle : d ≤ n := Nat.le_of_dvd (by omega) hdn
  by_cases hdn_eq : d = n
  · subst hdn_eq
    exact hpd
  · exact absurd hdvd (hp.not_dvd_of_lt hdpos (by omega))

end MetaMathlibExt
