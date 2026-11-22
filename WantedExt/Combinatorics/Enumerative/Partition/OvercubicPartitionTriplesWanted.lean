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
# Congruences for overcubic partition triples

Statements from S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar,
*Divisibility Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80.

`bt(n)` counts overcubic partition triples of `n`: ordered triples of overcubic partitions
(Kim's overlined cubic partitions) with total size `n`. Its generating function is
`∑ bt(n) q^n = f_4^3 / (f_1^6 f_2^3)`, where `f_k = (q^k; q^k)_∞` is `qEulerProduct k`,
written `𝔣 k` below. We define `bt(n)` as the `n`th coefficient of that quotient in `ℤ⟦X⟧`
(the denominator has constant coefficient `1`, so it is a unit). The paper's `E_k` is `f_k`.
Products of `f_k` are stated with denominators cleared.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- The generating function `∑ bt(n) q^n = f_4^3 / (f_1^6 f_2^3)` of overcubic partition
triples, as an integer power series.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1; the
same generating function is quoted from this paper by Saikia and Sarma (arXiv:2411.00013,
eq. (2)) and by Chen, Jin, and Yao (arXiv:2504.06941, eq. (1.1)). -/
noncomputable def overcubicTripleSeries : ℤ⟦X⟧ :=
  𝔣 4 ^ 3 * invOfUnit (𝔣 1 ^ 6 * 𝔣 2 ^ 3) 1

/-- `bt(n)`, the number of overcubic partition triples of `n`, defined as the `n`th
coefficient of `f_4^3 / (f_1^6 f_2^3)` (integer-valued).

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
noncomputable def overcubicTripleCount (n : ℕ) : ℤ :=
  coeff n overcubicTripleSeries

/-- The defining identity `f_1^6 f_2^3 ∑ bt(n) q^n = f_4^3`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
theorem overcubicTripleCount_generatingFunction :
    𝔣 1 ^ 6 * 𝔣 2 ^ 3 * PowerSeries.mk overcubicTripleCount = 𝔣 4 ^ 3 := by
  have hmk : PowerSeries.mk overcubicTripleCount = overcubicTripleSeries := by
    ext n
    simp [overcubicTripleCount]
  have hc : constantCoeff (𝔣 1 ^ 6 * 𝔣 2 ^ 3) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, overcubicTripleSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- `bt(0) = 1`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
theorem overcubicTripleCount_zero : overcubicTripleCount 0 = 1 := by
  have h := congrArg (coeff 0) overcubicTripleCount_generatingFunction
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4), one_pow, one_mul] at h
  simpa using h

/-- `f_1^2 = f_2 f_8^5 / (f_4^2 f_16^2) - 2 q f_2 f_16^2 / f_8`, stated with denominators
cleared (both sides multiplied by `f_4^2 f_8 f_16^2`).

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 1, eq. (39)
(`integers-2024-A80-lem-1`). -/
public theorem_wanted f1_sq_two_dissection :
    𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 * 𝔣 16 ^ 2 =
      𝔣 2 * 𝔣 8 ^ 6 - 2 * X * 𝔣 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4

/-- `1 / f_1^2 = f_8^5 / (f_2^5 f_16^2) + 2 q f_4^2 f_16^2 / (f_2^5 f_8)`, stated with
denominators cleared (both sides multiplied by `f_1^2 f_2^5 f_8 f_16^2`).

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 1, eq. (40)
(`integers-2024-A80-lem-1`). -/
public theorem_wanted one_div_f1_sq_two_dissection :
    𝔣 2 ^ 5 * 𝔣 8 * 𝔣 16 ^ 2 =
      𝔣 1 ^ 2 * 𝔣 8 ^ 6 + 2 * X * 𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4

/-- `f_1^3 = f_6 f_9^6 / (f_3 f_18^3) + 4 q^3 f_3^2 f_18^6 / (f_6^2 f_9^3) - 3 q f_9^3`,
stated with denominators cleared (both sides multiplied by `f_3 f_6^2 f_9^3 f_18^3`).

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 2, eq. (41)
(merged into the record `integers-2024-A80-lem-1`). -/
public theorem_wanted f1_cube_three_dissection :
    𝔣 1 ^ 3 * 𝔣 3 * 𝔣 6 ^ 2 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3 =
      𝔣 6 ^ 3 * 𝔣 9 ^ 9 + 4 * X ^ 3 * 𝔣 3 ^ 3 * 𝔣 18 ^ 9
        - 3 * X * 𝔣 3 * 𝔣 6 ^ 2 * 𝔣 9 ^ 6 * 𝔣 18 ^ 3

/-- For all `n, α ≥ 0`: `bt(8n+7) ≡ 0 (mod 32)`, `bt(8n+5) ≡ 0 (mod 8)`,
`bt(72n+33) ≡ 0 (mod 8)`, `bt(72n+57) ≡ 0 (mod 8)`, and
`bt(8·9^{α+2} n + 33·9^{α+1}) ≡ 0 (mod 8)`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 1,
eqs. (2)-(6) (`integers-2024-A80-thm-1`). -/
public theorem_wanted overcubicTripleCount_congruences_odd_args (n α : ℕ) :
    overcubicTripleCount (8 * n + 7) ≡ 0 [ZMOD 32] ∧
      overcubicTripleCount (8 * n + 5) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (72 * n + 33) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (72 * n + 57) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (8 * 9 ^ (α + 2) * n + 33 * 9 ^ (α + 1)) ≡ 0 [ZMOD 8]

/-- For all `n ≥ 0`, `bt(24n+1) ≡ 2 [q^n] f_1 (mod 4)`, i.e.
`∑ bt(24n+1) q^n ≡ 2 f_1 (mod 4)`. This is the `α = 0` case of the paper's statement.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 2,
eq. (7), case `α = 0` (`integers-2024-A80-thm-2`). -/
public theorem_wanted overcubicTripleCount_twentyFour_mul_add_one (n : ℕ) :
    overcubicTripleCount (24 * n + 1) ≡ 2 * coeff n (𝔣 1) [ZMOD 4]

/-- For all `n, α ≥ 0`: `bt(16n+14) ≡ bt(16n+10) ≡ 0 (mod 16)`,
`bt(144n+66) ≡ bt(144n+114) ≡ 0 (mod 8)`, `bt(1296n+594) ≡ bt(1296n+1026) ≡ 0 (mod 8)`,
`bt(16·9^{α+3} n + 66·9^{α+2}) ≡ 0 (mod 8)`, and `bt(432n+306) ≡ bt(48n+34) (mod 8)`.
The paper's congruence (16), `bt(432n+18) ≡ bt(48n+2) (mod 8)`, is omitted: it fails at
`n = 0`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 4,
eqs. (9)-(15) and (17) (`integers-2024-A80-thm-4`). -/
public theorem_wanted overcubicTripleCount_congruences_two_mod_four_args (n α : ℕ) :
    overcubicTripleCount (16 * n + 14) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (16 * n + 10) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (144 * n + 66) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (144 * n + 114) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (1296 * n + 594) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (1296 * n + 1026) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (16 * 9 ^ (α + 3) * n + 66 * 9 ^ (α + 2)) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (432 * n + 306) ≡ overcubicTripleCount (48 * n + 34) [ZMOD 8]

/-- For all `n, α ≥ 0`: `bt(32n+28) ≡ bt(32n+20) ≡ 0 (mod 16)`, `bt(64n+56) ≡ 0 (mod 8)`,
`bt(576n+408) ≡ 0 (mod 8)`, `bt(5184n+216) ≡ bt(5184n+3672) ≡ 0 (mod 8)`, and
`bt(64·81^{α+2} n + 216·81^{α+1}) ≡ 0 (mod 8)`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 5,
eqs. (18)-(24) (`integers-2024-A80-thm-5`). -/
public theorem_wanted overcubicTripleCount_congruences_four_mul_args (n α : ℕ) :
    overcubicTripleCount (32 * n + 28) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (32 * n + 20) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (64 * n + 56) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (576 * n + 408) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (5184 * n + 216) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (5184 * n + 3672) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (64 * 81 ^ (α + 2) * n + 216 * 81 ^ (α + 1)) ≡ 0 [ZMOD 8]

/-- For all `n ≥ 0`, `bt(576n+24) ≡ 4 [q^n] f_1 (mod 8)`, i.e.
`∑ bt(576n+24) q^n ≡ 4 f_1 (mod 8)`. This is the `α = 0` case of the paper's statement.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 6,
eq. (25), case `α = 0` (`integers-2024-A80-thm-6`). -/
public theorem_wanted overcubicTripleCount_fiveHundredSeventySix_mul_add_twentyFour (n : ℕ) :
    overcubicTripleCount (576 * n + 24) ≡ 4 * coeff n (𝔣 1) [ZMOD 8]

/-- For all `n, α ≥ 0`: `bt(64n+40) ≡ 0 (mod 8)`, `bt(576n+264) ≡ bt(576n+456) ≡ 0 (mod 8)`,
and `bt(64·9^{α+2} n + 264·9^{α+1}) ≡ 0 (mod 8)`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 8,
eqs. (27)-(30) (`integers-2024-A80-thm-8`). -/
public theorem_wanted overcubicTripleCount_congruences_eight_mod_sixteen_args (n α : ℕ) :
    overcubicTripleCount (64 * n + 40) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (576 * n + 264) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (576 * n + 456) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (64 * 9 ^ (α + 2) * n + 264 * 9 ^ (α + 1)) ≡ 0 [ZMOD 8]

/-- For all `n ≥ 0`, `bt(192n+8) ≡ 2 [q^n] f_1 (mod 4)`, i.e.
`∑ bt(192n+8) q^n ≡ 2 f_1 (mod 4)`. This is the `α = 0` case of the paper's statement.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 9,
eq. (31), case `α = 0` (`integers-2024-A80-thm-9`). -/
public theorem_wanted overcubicTripleCount_oneHundredNinetyTwo_mul_add_eight (n : ℕ) :
    overcubicTripleCount (192 * n + 8) ≡ 2 * coeff n (𝔣 1) [ZMOD 4]

/-- For all `n, α ≥ 0`: `bt(64n+48) ≡ 0`, `bt(128n+80) ≡ 0`, `bt(128n+96) ≡ 0`,
`bt(256n+160) ≡ 0`, `bt(256n+32) ≡ bt(128n+16)`, and `bt(256·2^α n + 192) ≡ 0`, all modulo `4`.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 11,
eqs. (33)-(38) (`integers-2024-A80-thm-11`). -/
public theorem_wanted overcubicTripleCount_congruences_sixteen_mul_args (n α : ℕ) :
    overcubicTripleCount (64 * n + 48) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (128 * n + 80) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (128 * n + 96) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (256 * n + 160) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (256 * n + 32) ≡ overcubicTripleCount (128 * n + 16) [ZMOD 4] ∧
      overcubicTripleCount (256 * 2 ^ α * n + 192) ≡ 0 [ZMOD 4]

end

end MetaMathlibExt
