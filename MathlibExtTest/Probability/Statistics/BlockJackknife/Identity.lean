/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.BlockJackknife.Identity
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tests for the delete-one jackknife covariance identity

The smallest nondegenerate case is two scalar blocks `(0, 1)`, giving `V_jack = 1/4` both from
the identity and directly from the leave-one-out definition. The remaining examples cover
identical blocks, dimension zero, and a rank-one two-block sample in `ℝ²`.
-/

@[expose] public section

open Finset Matrix
open MathlibExt.Probability.Statistics.BlockJackknife

namespace MathlibExtTest.Probability.Statistics.BlockJackknife

-- Smallest nondegenerate sample size and dimension: `B = 2`, `d = 1`, `z = (0, 1)`.
example : jackCov (fun b : Fin 2 => fun _ : Fin 1 => (b : ℝ)) = fun _ _ => 1 / 4 := by
  rw [jackCov_eq (by simp)]
  ext i j
  simp [mean, vecMulVec, Fin.sum_univ_two]
  norm_num

-- The same value straight from the leave-one-out definition, without using the identity.
example : jackCov (fun b : Fin 2 => fun _ : Fin 1 => (b : ℝ)) = fun _ _ => 1 / 4 := by
  have h : ∀ (b : Fin 2) (f : Fin 2 → Fin 1 → ℝ), ∑ c ∈ univ.erase b, f c = ∑ c, f c - f b :=
    fun b f => by rw [← add_sum_erase univ f (mem_univ b)]; abel
  ext i j
  simp only [jackCov, looMean, mean, h, Fin.sum_univ_two]
  simp [vecMulVec]
  norm_num

-- Zero-variance boundary: identical blocks give `V_jack = 0`.
example {ι n : Type*} [Fintype ι] [DecidableEq ι] (hB : 2 ≤ Fintype.card ι) (v : n → ℝ) :
    jackCov (fun _ : ι => v) = 0 := by
  have hB0 : (Fintype.card ι : ℝ) ≠ 0 := by
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hB
    linarith
  have hm : mean (fun _ : ι => v) = v := by
    rw [mean, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hB0,
      one_smul]
  rw [jackCov_eq hB, hm]
  simp

-- Rank-zero boundary: dimension zero gives the zero matrix.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → Fin 0 → ℝ) : jackCov z = 0 :=
  Subsingleton.elim _ _

-- Rank one: a two-block sample in `ℝ²` gives `(1/4)(v - u)(v - u)ᵀ`.
example (u v : Fin 2 → ℝ) :
    jackCov ![u, v] = (1 / 4 : ℝ) • vecMulVec (v - u) (v - u) := by
  rw [jackCov_eq (by simp)]
  have hm : mean ![u, v] = (1 / 2 : ℝ) • (u + v) := by
    simp [mean, Fin.sum_univ_two]
  rw [hm, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.card_fin]
  ext i j
  simp [vecMulVec]
  ring

#print axioms MathlibExt.Probability.Statistics.BlockJackknife.looMean_sub_mean
#print axioms MathlibExt.Probability.Statistics.BlockJackknife.jackCov_eq

end MathlibExtTest.Probability.Statistics.BlockJackknife
