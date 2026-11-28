/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the alternating stride sum series

Concrete stride sums and instances of convergence to the Riemann zeta function.
-/

namespace MathlibExtTest.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta

open Filter Topology

example : MetaMathlibExt.strideAlternatingSum 2 1 4 = -(1 / 4 : ℝ) := by
  have hbase := MetaMathlibExt.strideAlternatingSum_of_le (q := 2) (t := 1) (n := 2)
    (by decide) (by decide)
  have hstep := MetaMathlibExt.strideAlternatingSum_add (q := 2) (t := 1) (n := 2)
    (by decide) (by decide)
  norm_num [hstep, hbase]

example : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
    (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
      MetaMathlibExt.strideAlternatingSum 1 1 (n + 1) : ℝ) : ℂ))
    atTop (𝓝 (riemannZeta 2)) := by
  convert MetaMathlibExt.tendsto_strideAlternatingSum_riemannZeta
    1 1 (by decide) (by decide) using 1 <;> norm_num [add_assoc]

example : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
    (2 * ((n : ℝ) + 1) + 3) / (((n : ℝ) + 1) * ((n : ℝ) + 4)) *
      MetaMathlibExt.strideAlternatingSum 3 2 (n + 1) : ℝ) : ℂ))
    atTop (𝓝 (riemannZeta 3)) := by
  convert MetaMathlibExt.tendsto_strideAlternatingSum_riemannZeta
    3 2 (by decide) (by decide) using 1 <;> norm_num [add_assoc]

-- Check the first two terms at p = 0, including the negative second stride sum.
example : (∑ n ∈ Finset.range 2,
    (((n : ℝ) + 1) ^ (0 + 1) + ((n : ℝ) + 1 + 1) ^ (0 + 1)) /
      (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) ^ (0 + 1) *
        MetaMathlibExt.strideAlternatingSum 1 1 (n + 1)) = 13 / 12 := by
  have h₁ := MetaMathlibExt.strideAlternatingSum_of_le (q := 1) (t := 1) (n := 1)
    (by decide) (by decide)
  have h₂ := MetaMathlibExt.strideAlternatingSum_add (q := 1) (t := 1) (n := 1)
    (by decide) (by decide)
  norm_num [Finset.sum_range_succ, h₁, h₂]

-- Check the cubed weight through the first stride shift (q = p = 2).
example : (∑ n ∈ Finset.range 3,
    (((n : ℝ) + 1) ^ (2 + 1) + ((n : ℝ) + 1 + 2) ^ (2 + 1)) /
      (((n : ℝ) + 1) * ((n : ℝ) + 1 + 2)) ^ (2 + 1) *
        MetaMathlibExt.strideAlternatingSum 2 1 (n + 1)) = 1396213 / 1296000 := by
  have h₁ := MetaMathlibExt.strideAlternatingSum_of_le (q := 2) (t := 1) (n := 1)
    (by decide) (by decide)
  have h₂ := MetaMathlibExt.strideAlternatingSum_of_le (q := 2) (t := 1) (n := 2)
    (by decide) (by decide)
  have h₃ := MetaMathlibExt.strideAlternatingSum_add (q := 2) (t := 1) (n := 1)
    (by decide) (by decide)
  norm_num [Finset.sum_range_succ, h₁, h₂, h₃]

-- The public limit theorem specializes to ζ(4) for q = 2, t = 1, p = 2.
example : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
    (((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1 + 2) ^ 3) /
      (((n : ℝ) + 1) * ((n : ℝ) + 1 + 2)) ^ 3 *
        MetaMathlibExt.strideAlternatingSum 2 1 (n + 1) : ℝ) : ℂ))
    atTop (𝓝 (riemannZeta 4)) := by
  convert MetaMathlibExt.tendsto_strideAlternatingSum_riemannZeta_add 2 1 2
    (by decide) (by decide) ⟨1, rfl⟩ using 1
  norm_num

-- Independently check the limit for q = t = 1, p = 2 by shifting absolutely convergent series.
example : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
    (((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1 + 1) ^ 3) /
      (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) ^ 3 *
        MetaMathlibExt.strideAlternatingSum 1 1 (n + 1) : ℝ) : ℂ))
    atTop (𝓝 (riemannZeta 4)) := by
  let a (n : ℕ) := MetaMathlibExt.strideAlternatingSum 1 1 (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3
  let g (n : ℕ) := 1 / (n : ℝ) ^ 4
  have hrec (n : ℕ) := MetaMathlibExt.strideAlternatingSum_add (q := 1) (t := 1) (n := n + 1)
    (by decide) (Nat.succ_pos n)
  have hfirst : MetaMathlibExt.strideAlternatingSum 1 1 1 = 1 := by
    simpa using MetaMathlibExt.strideAlternatingSum_of_le (q := 1) (t := 1) (n := 1)
      (by decide) (by decide)
  have hbound (n : ℕ) : ‖MetaMathlibExt.strideAlternatingSum 1 1 (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    induction n with
    | zero => norm_num [hfirst]
    | succ n ih =>
      rw [hrec n]
      have hle : (1 : ℝ) / ((n + 1 + 1 : ℕ) : ℝ) ^ 1 ≤ 1 := by
        rw [pow_one]
        exact (div_le_one (by positivity)).mpr (Nat.one_le_cast.mpr (by omega))
      calc
        _ ≤ ‖(1 : ℝ) / ((n + 1 + 1 : ℕ) : ℝ) ^ 1‖ +
            ‖MetaMathlibExt.strideAlternatingSum 1 1 (n + 1)‖ := norm_sub_le _ _
        _ ≤ 1 + ((n + 1 : ℕ) : ℝ) := by
          rw [Real.norm_of_nonneg (by positivity)]
          exact add_le_add hle ih
        _ = _ := by push_cast; ring
  have ha : Summable a := by
    have h₂ : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by decide)
    apply ((summable_nat_add_iff 1).mpr h₂).of_norm_bounded
    intro n
    dsimp only [a]
    rw [norm_div, norm_pow, Real.norm_natCast]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (hbound n) (by positivity)
      _ = _ := by field_simp
  have hg : Summable g := Real.summable_one_div_nat_pow.mpr (by decide)
  have ha' : Summable (fun n => a (n + 1)) := (summable_nat_add_iff 1).mpr ha
  have hgs : Summable (fun n => g (n + 1)) := (summable_nat_add_iff 1).mpr hg
  have hgs' : Summable (fun n => g (n + 1 + 1)) := (summable_nat_add_iff 1).mpr hgs
  have h := ((ha.sub ha').add hgs').hasSum.tendsto_sum_nat
  rw [Summable.tsum_add (ha.sub ha') hgs', ha.tsum_sub ha', ha.tsum_eq_zero_add,
    add_sub_cancel_right] at h
  have h₀ : a 0 = g 1 := by norm_num [a, g, hfirst]
  have hshift : (∑' n, g (n + 1)) = g 1 + ∑' n, g (n + 1 + 1) := by
    simpa only [zero_add] using hgs.tsum_eq_zero_add
  rw [h₀, ← hshift] at h
  have hz : (↑(∑' n, g (n + 1)) : ℂ) = riemannZeta 4 := by
    have heq : (↑(∑' n, g n) : ℂ) = riemannZeta 4 := by
      rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, zeta_nat_eq_tsum_of_gt_one (by decide)]
      simpa [g] using (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) g)
    rw [hg.tsum_eq_zero_add] at heq
    simpa [g] using heq
  have hlim := (Complex.continuous_ofReal.tendsto _).comp h
  rw [hz] at hlim
  apply hlim.congr
  intro N
  apply congrArg Complex.ofReal
  refine Finset.sum_congr rfl fun n _ => ?_
  dsimp [a, g]
  rw [hrec n]
  push_cast
  field_simp
  ring

end MathlibExtTest.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta
