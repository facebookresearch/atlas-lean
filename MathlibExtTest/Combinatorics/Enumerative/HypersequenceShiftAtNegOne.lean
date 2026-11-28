/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSmallCases
import MathlibExt.Combinatorics.Enumerative.HypersequenceShiftAtNegOne

/-! # Tests for Parisse's hypersequence coefficient shifts -/

open Finset MetaMathlibExt

-- The second elementary symmetric value on `[-1, 0, 1]` and its expansion on `[0, 1, 2]`.
example :
    ((Icc 1 3).val.map fun i : ℕ => (-2 : ℤ) + i).esymm 2 = -1 ∧
      (∑ i ∈ range 3, ((3 - 2 + i).choose i : ℤ) * (-1) ^ i *
        ((Icc 1 3).val.map fun t : ℕ => (-1 : ℤ) + t).esymm (2 - i)) = -1 := by
  decide +kernel

-- Odd column signs matter in this shift, and the column above the diagonal stays zero.
example :
    hyperseqB (-2) 3 1 = 1 ∧
      (∑ i ∈ Icc 1 3, (-1 : ℤ) ^ (i - 1) * (i.choose 1 : ℤ) * (-1) ^ (i - 1) *
        hyperseqB (-1) 3 i) = 1 ∧
      hyperseqB (-2) 3 4 = 0 ∧
      (∑ i ∈ Icc 4 3, (-1 : ℤ) ^ (i - 4) * (i.choose 4 : ℤ) * (-1) ^ (i - 4) *
        hyperseqB (-1) 3 i) = 0 := by
  decide +kernel

-- Independently read the degree-one coefficient used in the signed-coefficient API.
open Polynomial in
example : (∏ i ∈ Icc (1 : ℕ) 3, (X + C ((-2 : ℤ) + (i : ℤ)))).coeff 1 = -1 := by
  rw [Finset.prod_X_add_C_coeff _ (fun i : ℕ => (-2 : ℤ) + i) (by decide)]
  decide +kernel

-- Compute both sides by the public order-one formula `p_{ℓ,1}(1, y) = y^ℓ - (1 + y)^ℓ`.
example :
    alternatingBinomialPowerSum 3 1 1 2 = -19 ∧
      (∑ i ∈ Icc 1 3, ((3 : ℕ).choose i : ℂ) * 2 ^ (3 - i) *
        alternatingBinomialPowerSum i 1 1 0) = -19 := by
  have h (i : ℕ) (y : ℂ) := (alternatingBinomialPowerSum_small_cases 1 y i 1).2.1
  have hIcc : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  constructor
  · norm_num [h]
  · norm_num [hIcc, sum_insert, h, Nat.choose]

-- Above the diagonal, the order-two sum cancels directly and the expansion has no terms.
example :
    alternatingBinomialPowerSum 1 2 1 (-1) = 0 ∧
      (∑ i ∈ Icc 2 1, ((1 : ℕ).choose i : ℂ) * (-1) ^ (1 - i) *
        alternatingBinomialPowerSum i 2 1 0) = 0 := by
  rw [(alternatingBinomialPowerSum_small_cases 1 (-1) 1 2).2.2.1, Icc_eq_empty_of_lt (by decide),
    sum_empty]
  norm_num

-- The proved theorem is usable without importing the wanted module.
example :
    hyperseqB (-2) 3 1 =
      ∑ i ∈ Icc 1 3, (-1 : ℤ) ^ (i - 1) * (i.choose 1 : ℤ) * (-1) ^ (i - 1) *
        hyperseqB (-1) 3 i := by
  simpa using (hyperseq_entries_eq_sum_at_neg_one (-2)).2.1 3 1
