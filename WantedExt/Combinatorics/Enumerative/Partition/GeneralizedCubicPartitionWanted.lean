/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

/-!
# Congruences for generalized cubic partitions modulo primes

Statements from Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions
Modulo Primes*, INTEGERS 25 (2025), Article A20.

A generalized cubic partition of `n` (Amdeberhan, Sellers, and Singh) is a partition of `n`
whose even parts may appear in `c ≥ 1` colors; `a_c(n)` counts them, with
`∑ a_c(n) qⁿ = 1/(f_1 f_2^{c-1})`, where `f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written
`𝔣 k` below. We define `a_c(n)` as the `n`th coefficient of that quotient in `ℤ⟦X⟧` (the
denominator has constant coefficient `1`, so it is a unit). `c = 1` gives the partition
function and `c = 2` Chan's cubic partitions.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- The generating function `∑ a_c(n) qⁿ = 1/(f_1 f_2^{c-1})` of generalized cubic
partitions (even parts in `c` colors), as an integer power series; meaningful for `c ≥ 1`.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionSeries (c : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (𝔣 1 * 𝔣 2 ^ (c - 1)) 1

/-- `a_c(n)`, the number of generalized cubic partitions of `n` with even parts in `c`
colors, defined as the `n`th coefficient of `1/(f_1 f_2^{c-1})`.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionCount (c n : ℕ) : ℤ :=
  coeff n (generalizedCubicPartitionSeries c)

/-- The defining identity `f_1 f_2^{c-1} ∑ a_c(n) qⁿ = 1`.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_generatingFunction (c : ℕ) :
    𝔣 1 * 𝔣 2 ^ (c - 1) * PowerSeries.mk (generalizedCubicPartitionCount c) = 1 := by
  have hmk : PowerSeries.mk (generalizedCubicPartitionCount c) =
      generalizedCubicPartitionSeries c := by
    ext n
    simp [generalizedCubicPartitionCount]
  have hc : constantCoeff (𝔣 1 * 𝔣 2 ^ (c - 1)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, generalizedCubicPartitionSeries, mul_invOfUnit _ _ hc]

/-- `a_c(0) = 1`.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_zero (c : ℕ) :
    generalizedCubicPartitionCount c 0 = 1 := by
  have h := congrArg (coeff 0) (generalizedCubicPartitionCount_generatingFunction c)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    one_pow, one_mul, map_one] at h
  simpa using h

/-- **Amdeberhan–Sellers–Singh congruences**: for all `n ≥ 0`,
`a_3(7n + 4) ≡ 0 (mod 7)` and `a_5(11n + 10) ≡ 0 (mod 11)`.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 1 (quoting Amdeberhan, Sellers, and
Singh), Equations (1) and (2). -/
public theorem_wanted generalizedCubicPartitionCount_seven_eleven (n : ℕ) :
    (7 : ℤ) ∣ generalizedCubicPartitionCount 3 (7 * n + 4) ∧
      (11 : ℤ) ∣ generalizedCubicPartitionCount 5 (11 * n + 10)

/-- For a prime `p ≡ 5, 7 (mod 8)` and `0 ≤ l ≤ p - 1` with `p ∣ 8l + 3`,
`a_{p-4}(pn + l) ≡ 0 (mod p)` for all `n ≥ 0`. The bound `l ≤ p - 1` is dropped: a larger
`l` reduces to `l mod p`, which satisfies the same divisibility.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 2, Equation (9). -/
public theorem_wanted generalizedCubicPartitionCount_prime_five_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) {l : ℕ} (hdvd : p ∣ 8 * l + 3) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 4) (p * n + l)

/-- For a prime `p ≥ 7` with `p ≡ 3, 7 (mod 8)`,
`a_{p-6}(pn + 13(p² - 1)/24) ≡ 0 (mod p)` for all `n ≥ 0` (`24 ∣ p² - 1`, so the shift is
an exact natural-number quotient).

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 3, Equation (13). -/
public theorem_wanted generalizedCubicPartitionCount_prime_three_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hp8 : p % 8 = 3 ∨ p % 8 = 7) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 6) (p * n + 13 * (p ^ 2 - 1) / 24)

end

end MetaMathlibExt
