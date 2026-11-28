/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaStrideSeriesDirichletEta
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the signed stride series for the Dirichlet eta function -/

namespace MathlibExtTest.NumberTheory.ZetaStrideSeriesDirichletEta

open Filter Topology MetaMathlibExt

-- Odd stride: the two terms within the second signed stride sum have the same sign.
example : (∑ n ∈ Finset.range 2,
    (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) *
      strideSignedSum 1 2 (n + 1)) = 11 / 24 := by
  have h₁ := strideSignedSum_of_le (q := 1) (t := 2) (n := 1) (by decide) (by decide)
  have h₂ := strideSignedSum_add (q := 1) (t := 2) (n := 1) (by decide) (by decide)
  norm_num [Finset.sum_range_succ, h₁, h₂]

-- Even stride: the third signed stride sum includes a negative contribution from index 1.
example : (∑ n ∈ Finset.range 3,
    (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 2)) *
      strideSignedSum 2 2 (n + 1)) = 1451 / 2160 := by
  have h₁ := strideSignedSum_of_le (q := 2) (t := 2) (n := 1) (by decide) (by decide)
  have h₂ := strideSignedSum_of_le (q := 2) (t := 2) (n := 2) (by decide) (by decide)
  have h₃ := strideSignedSum_add (q := 2) (t := 2) (n := 1) (by decide) (by decide)
  norm_num [Finset.sum_range_succ, h₁, h₂, h₃]

-- Independently verify the limit at q = 1, t = 2 using the summable inverse squares
-- to give a uniform bound, and induction to cancel successive boundary terms.
example : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) *
      strideSignedSum 1 2 (n + 1))
    atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 3)) := by
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2
  let g (n : ℕ) : ℝ := (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 3
  let b (n : ℕ) : ℝ := (-1 : ℝ) ^ n * strideSignedSum 1 2 (n + 1) / ((n : ℝ) + 1)
  let w (n : ℕ) : ℝ :=
    (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) *
      strideSignedSum 1 2 (n + 1)
  have hbase := strideSignedSum_of_le (q := 1) (t := 2) (n := 1) (by decide) (by decide)
  have hrec (n : ℕ) :
      strideSignedSum 1 2 (n + 1 + 1) = r (n + 1) + strideSignedSum 1 2 (n + 1) := by
    simpa [r, Nat.cast_add] using
      strideSignedSum_add (q := 1) (t := 2) (n := n + 1) (by decide) (Nat.succ_pos n)
  have hT (n : ℕ) : strideSignedSum 1 2 (n + 1) = ∑ k ∈ Finset.range (n + 1), r k := by
    induction n with
    | zero => norm_num [hbase, r, Finset.sum_range_one]
    | succ n ih => rw [hrec n, Finset.sum_range_succ, ih, add_comm]
  have hw (n : ℕ) : w n = b n - b (n + 1) + g (n + 1) := by
    dsimp only [w, b, g]
    rw [hrec n, pow_succ (-1 : ℝ) n]
    simp only [r, Nat.cast_add, Nat.cast_one]
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hy : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [hx, hy]
    ring
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, w n) =
      (∑ n ∈ Finset.range (N + 1), g n) - b N := by
    induction N with
    | zero => norm_num [b, g, hbase, Finset.sum_range_one]
    | succ n ih => rw [Finset.sum_range_succ w n, ih, hw, Finset.sum_range_succ g (n + 1)]; ring
  have hr : Summable r := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have hb : Tendsto b atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => (∑' k, r k) / ((n : ℝ) + 1))
    · intro n
      dsimp only [b]
      rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hT,
        Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => by positivity),
        Real.norm_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (hr.sum_le_tsum _ (fun k _ => by positivity)) (by positivity)
    · simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)).const_div_atTop
          (∑' k, r k)
  have hgAbs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3))
  have hg : Summable g := hgAbs.of_norm_bounded fun n => by
    dsimp only [g]
    rw [norm_div, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      Real.norm_of_nonneg (by positivity)]
  have h := (hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub hb
  simp only [sub_zero] at h
  exact h.congr fun N => (hsum N).symm

-- A client can use the general theorem at an even stride without opening the definition.
example : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 2)) *
      strideSignedSum 2 2 (n + 1))
    atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 3)) :=
  tendsto_strideSignedSum_dirichletEta 2 2 (by decide) (by decide)

end MathlibExtTest.NumberTheory.ZetaStrideSeriesDirichletEta
