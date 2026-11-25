/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Delete-one jackknife covariance of a vector mean

For at least two block vectors `z b`, let `mean₋b` be the mean of the blocks other than `b`.
The delete-one jackknife covariance
`(B - 1)/B ∑_b (mean₋b - mean)(mean₋b - mean)ᵀ` equals
`[B(B - 1)]⁻¹ ∑_b (z b - mean)(z b - mean)ᵀ`.

This is a purely algebraic identity: there is no measure, independence assumption, or
consistency claim.

## Main definitions and results

* `BlockJackknife.mean`, `BlockJackknife.looMean`, and `BlockJackknife.jackCov`: the block mean,
  leave-one-out means, and jackknife covariance.
* `BlockJackknife.looMean_sub_mean`: each leave-one-out deviation is `-(B - 1)⁻¹` times the
  block's own deviation.
* `BlockJackknife.jackCov_eq`: the jackknife covariance identity.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.Statistics.BlockJackknife

variable {ι n : Type*} [Fintype ι] [DecidableEq ι]

/-- The mean of the block vectors. -/
noncomputable def mean (z : ι → n → ℝ) : n → ℝ := (Fintype.card ι : ℝ)⁻¹ • ∑ b, z b

/-- The leave-one-out mean, omitting block `b`. -/
noncomputable def looMean (z : ι → n → ℝ) (b : ι) : n → ℝ :=
  ((Fintype.card ι : ℝ) - 1)⁻¹ • ∑ c ∈ univ.erase b, z c

/-- The delete-one jackknife covariance `(B - 1)/B ∑_b (mean₋b - mean)(mean₋b - mean)ᵀ`. -/
noncomputable def jackCov (z : ι → n → ℝ) : Matrix n n ℝ :=
  (((Fintype.card ι : ℝ) - 1) / Fintype.card ι) •
    ∑ b, vecMulVec (looMean z b - mean z) (looMean z b - mean z)

/-- Each leave-one-out deviation is `-(B - 1)⁻¹` times the block's own deviation. -/
theorem looMean_sub_mean (hB : 2 ≤ Fintype.card ι) (z : ι → n → ℝ) (b : ι) :
    looMean z b - mean z = -((Fintype.card ι : ℝ) - 1)⁻¹ • (z b - mean z) := by
  have hB0 : (Fintype.card ι : ℝ) ≠ 0 := by
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hB
    linarith
  have hB1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hB
    linarith
  have hs : ∑ c ∈ univ.erase b, z c = ∑ c, z c - z b := by
    rw [← add_sum_erase univ z (mem_univ b)]; abel
  unfold looMean mean
  rw [hs]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  field_simp
  ring

/-- The jackknife covariance identity. -/
theorem jackCov_eq (hB : 2 ≤ Fintype.card ι) (z : ι → n → ℝ) :
    jackCov z = ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))⁻¹ •
      ∑ b, vecMulVec (z b - mean z) (z b - mean z) := by
  have hB0 : (Fintype.card ι : ℝ) ≠ 0 := by
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hB
    linarith
  have hB1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hB
    linarith
  unfold jackCov
  simp_rw [looMean_sub_mean hB, smul_vecMulVec, vecMulVec_smul, smul_smul, ← smul_sum, smul_smul]
  congr 1
  field_simp

end MathlibExt.Probability.Statistics.BlockJackknife
