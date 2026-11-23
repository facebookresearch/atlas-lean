/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group

@[expose] public section

/-!
# Ramanujan's factorial-series asymptotic expansion

This file proves the inverse-factorial asymptotic expansion in Part I, Chapter 3,
Section 8, Example 1 of Ramanujan's notebooks.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example1Asymptotic

private def sec8Ex1Prod (k : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range k, (z + ((i + 1 : ℕ) : ℂ))

private noncomputable def sec8Ex1Term (a : ℕ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ j * a j / sec8Ex1Prod (j + 1) z

private def sec8Ex1Coeff (n k : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + k) * (Nat.stirlingSecond n k : ℂ)

private noncomputable def sec8Ex1Approx (k N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), sec8Ex1Coeff n k / z ^ n

private noncomputable def sec8Ex1Recip (k : ℕ) (z : ℂ) : ℂ :=
  1 / sec8Ex1Prod k z

private noncomputable def sec8Ex1FiniteApprox (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * a j * sec8Ex1Approx (j + 1) (N + 1) z

private noncomputable def sec8Ex1Main (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    (-1 : ℂ) ^ j *
      (∑ k ∈ Finset.range (j + 1),
        a k * (Nat.stirlingSecond (j + 1) (k + 1) : ℂ)) / z ^ (j + 1)

private def sec8Ex1RealProd (x : ℝ) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (j + 1), (x + ((k + 1 : ℕ) : ℝ))

private lemma sec8Ex1RealProd_succ (x : ℝ) (j : ℕ) :
    sec8Ex1RealProd x (j + 1) =
      sec8Ex1RealProd x j * (x + ((j + 2 : ℕ) : ℝ)) := by
  rw [sec8Ex1RealProd, sec8Ex1RealProd, show j + 1 + 1 = (j + 1) + 1 from rfl,
    Finset.prod_range_succ]

private lemma sec8Ex1Prod_succ (k : ℕ) (z : ℂ) :
    sec8Ex1Prod (k + 1) z = sec8Ex1Prod k z * (z + ((k + 1 : ℕ) : ℂ)) := by
  rw [sec8Ex1Prod, sec8Ex1Prod, Finset.prod_range_succ]

private lemma sec8Ex1Prod_split (p n : ℕ) (z : ℂ) :
    sec8Ex1Prod (p + n) z = sec8Ex1Prod p z *
      ∏ i ∈ Finset.range n, (z + ((p + i + 1 : ℕ) : ℂ)) := by
  rw [sec8Ex1Prod, sec8Ex1Prod, Finset.prod_range_add]

private lemma sec8Ex1_negOne_pow_add_two (n : ℕ) :
    (-1 : ℂ) ^ (n + 2) = (-1 : ℂ) ^ n := by
  rw [pow_add]
  norm_num

private lemma sec8Ex1_negOne_pow_succ (n : ℕ) :
    (-1 : ℂ) ^ (n + 1) = -((-1 : ℂ) ^ n) := by
  rw [pow_succ]
  ring

private lemma sec8Ex1_negOne_pow_add_even (n m : ℕ) :
    (-1 : ℂ) ^ (n + 2 * m) = (-1 : ℂ) ^ n := by
  rw [pow_add, pow_mul]
  norm_num

private lemma sec8Ex1Coeff_succ_succ (n k : ℕ) :
    sec8Ex1Coeff (n + 1) (k + 1) =
      sec8Ex1Coeff n k - (k + 1 : ℂ) * sec8Ex1Coeff n (k + 1) := by
  rw [sec8Ex1Coeff, sec8Ex1Coeff, sec8Ex1Coeff,
    Nat.stirlingSecond_succ_succ]
  push_cast
  rw [show n + 1 + (k + 1) = (n + k) + 2 by omega,
    sec8Ex1_negOne_pow_add_two,
    show n + (k + 1) = (n + k) + 1 by omega,
    sec8Ex1_negOne_pow_succ]
  ring

private lemma sec8Ex1_sign_coeff (n j : ℕ) :
    (-1 : ℂ) ^ j * sec8Ex1Coeff (n + 1) (j + 1) =
      (-1 : ℂ) ^ n * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ) := by
  rw [sec8Ex1Coeff]
  calc
    (-1 : ℂ) ^ j *
        ((-1 : ℂ) ^ (n + 1 + (j + 1)) *
          (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) =
        ((-1 : ℂ) ^ j * (-1 : ℂ) ^ (n + 1 + (j + 1))) *
          (Nat.stirlingSecond (n + 1) (j + 1) : ℂ) := by ring
    _ = (-1 : ℂ) ^ (j + (n + 1 + (j + 1))) *
          (Nat.stirlingSecond (n + 1) (j + 1) : ℂ) := by rw [← pow_add]
    _ = (-1 : ℂ) ^ n * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ) := by
      rw [show j + (n + 1 + (j + 1)) = n + 2 * (j + 1) by omega,
        sec8Ex1_negOne_pow_add_even]

private lemma sec8Ex1_stirling_row_truncate (a : ℕ → ℂ) {n N : ℕ} (hn : n ≤ N) :
    (∑ j ∈ Finset.range (N + 1),
      a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) =
        ∑ j ∈ Finset.range (n + 1),
          a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
  intro j hjN hjn
  have hj : n + 1 < j + 1 := by
    simp only [Finset.mem_range] at hjn
    omega
  rw [Nat.stirlingSecond_eq_zero_of_lt hj]
  simp

private lemma sec8Ex1FiniteApprox_swap (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    sec8Ex1FiniteApprox a N z =
      ∑ n ∈ Finset.range (N + 2), ∑ j ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ j * a j * sec8Ex1Coeff n (j + 1) / z ^ n := by
  rw [sec8Ex1FiniteApprox]
  simp only [sec8Ex1Approx, show N + 1 + 1 = N + 2 by omega]
  calc
    (∑ j ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ j * a j *
        ∑ n ∈ Finset.range (N + 2), sec8Ex1Coeff n (j + 1) / z ^ n) =
        ∑ j ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 2),
          (-1 : ℂ) ^ j * a j * (sec8Ex1Coeff n (j + 1) / z ^ n) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range (N + 2), ∑ j ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ j * a j * (sec8Ex1Coeff n (j + 1) / z ^ n) :=
      Finset.sum_comm
    _ = ∑ n ∈ Finset.range (N + 2), ∑ j ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ j * a j * sec8Ex1Coeff n (j + 1) / z ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro j hj
      ring

private lemma sec8Ex1FiniteApprox_row (a : ℕ → ℂ) {n N : ℕ} (hn : n ≤ N) (z : ℂ) :
    (∑ j ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ j * a j * sec8Ex1Coeff (n + 1) (j + 1) / z ^ (n + 1)) =
        (-1 : ℂ) ^ n *
          (∑ j ∈ Finset.range (n + 1),
            a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) / z ^ (n + 1) := by
  calc
    (∑ j ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ j * a j * sec8Ex1Coeff (n + 1) (j + 1) / z ^ (n + 1)) =
        ∑ j ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ n *
            (a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) / z ^ (n + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (-1 : ℂ) ^ j * a j * sec8Ex1Coeff (n + 1) (j + 1) / z ^ (n + 1) =
            a j * ((-1 : ℂ) ^ j * sec8Ex1Coeff (n + 1) (j + 1)) /
              z ^ (n + 1) := by ring
        _ = a j *
            ((-1 : ℂ) ^ n * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) /
              z ^ (n + 1) := by rw [sec8Ex1_sign_coeff]
        _ = (-1 : ℂ) ^ n *
            (a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) /
              z ^ (n + 1) := by ring
    _ = (-1 : ℂ) ^ n *
        (∑ j ∈ Finset.range (N + 1),
          a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) / z ^ (n + 1) := by
      rw [Finset.mul_sum, Finset.sum_div]
    _ = (-1 : ℂ) ^ n *
        (∑ j ∈ Finset.range (n + 1),
          a j * (Nat.stirlingSecond (n + 1) (j + 1) : ℂ)) / z ^ (n + 1) := by
      rw [sec8Ex1_stirling_row_truncate a hn]

private lemma sec8Ex1FiniteApprox_eq_main (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    sec8Ex1FiniteApprox a N z = sec8Ex1Main a N z := by
  rw [sec8Ex1FiniteApprox_swap, Finset.sum_range_succ']
  have hzero : (∑ j ∈ Finset.range (N + 1),
      (-1 : ℂ) ^ j * a j * sec8Ex1Coeff 0 (j + 1) / z ^ 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [sec8Ex1Coeff]
  rw [hzero, add_zero, sec8Ex1Main]
  apply Finset.sum_congr rfl
  intro n hn
  apply sec8Ex1FiniteApprox_row a (z := z)
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)

private lemma sec8Ex1Coeff_div_succ (n k : ℕ) (z : ℂ) :
    sec8Ex1Coeff (n + 1) (k + 1) / z ^ (n + 1) =
      sec8Ex1Coeff n k / z ^ n / z -
        (k + 1 : ℂ) * (sec8Ex1Coeff n (k + 1) / z ^ n) / z := by
  rw [sec8Ex1Coeff_succ_succ, pow_succ]
  ring

private lemma sec8Ex1Approx_succ (k N : ℕ) (z : ℂ) :
    sec8Ex1Approx (k + 1) (N + 1) z =
      sec8Ex1Approx k N z / z - (k + 1 : ℂ) * sec8Ex1Approx (k + 1) N z / z := by
  rw [sec8Ex1Approx, Finset.sum_range_succ']
  have hzero : sec8Ex1Coeff 0 (k + 1) = 0 := by
    simp [sec8Ex1Coeff]
  rw [hzero, zero_div, add_zero, sec8Ex1Approx, sec8Ex1Approx]
  calc
    (∑ n ∈ Finset.range (N + 1), sec8Ex1Coeff (n + 1) (k + 1) / z ^ (n + 1)) =
        ∑ n ∈ Finset.range (N + 1),
          (sec8Ex1Coeff n k / z ^ n / z -
            (k + 1 : ℂ) * (sec8Ex1Coeff n (k + 1) / z ^ n) / z) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sec8Ex1Coeff_div_succ n k z
    _ = (∑ n ∈ Finset.range (N + 1), sec8Ex1Coeff n k / z ^ n) / z -
        (k + 1 : ℂ) *
          (∑ n ∈ Finset.range (N + 1), sec8Ex1Coeff n (k + 1) / z ^ n) / z := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [← Finset.sum_div]
      · rw [← Finset.sum_div, ← Finset.mul_sum]

private lemma sec8Ex1Recip_succ (k : ℕ) (z : ℂ) (hz : z ≠ 0)
    (hp : sec8Ex1Prod k z ≠ 0) (hfac : z + ((k + 1 : ℕ) : ℂ) ≠ 0) :
    sec8Ex1Recip (k + 1) z =
      sec8Ex1Recip k z / z - (k + 1 : ℂ) * sec8Ex1Recip (k + 1) z / z := by
  rw [sec8Ex1Recip, sec8Ex1Recip, sec8Ex1Prod_succ]
  field_simp
  push_cast
  ring

private lemma sec8Ex1_norm_le_norm_add_nat (z : ℂ) (hz : 0 ≤ z.re) (m : ℕ) :
    ‖z‖ ≤ ‖z + (m : ℂ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + (m : ℂ)))).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im,
    add_zero]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

private lemma sec8Ex1Prod_ne_zero (z : ℂ) (hre : 0 ≤ z.re) (hnorm : 1 ≤ ‖z‖)
    (k : ℕ) : sec8Ex1Prod k z ≠ 0 := by
  rw [sec8Ex1Prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hnorm)
    (sec8Ex1_norm_le_norm_add_nat z hre (i + 1))

private lemma sec8Ex1_pow_norm_le_norm_prod (z : ℂ) (hre : 0 ≤ z.re) (k : ℕ) :
    ‖z‖ ^ k ≤ ‖sec8Ex1Prod k z‖ := by
  induction k with
  | zero => simp [sec8Ex1Prod]
  | succ k ih =>
      rw [sec8Ex1Prod_succ, norm_mul, pow_succ]
      exact mul_le_mul ih (sec8Ex1_norm_le_norm_add_nat z hre (k + 1))
        (norm_nonneg z) (norm_nonneg (sec8Ex1Prod k z))

private lemma sec8Ex1Approx_zero_succ (k : ℕ) (z : ℂ) :
    sec8Ex1Approx (k + 1) 0 z = 0 := by
  simp [sec8Ex1Approx, sec8Ex1Coeff]

private lemma sec8Ex1Approx_zero (N : ℕ) (z : ℂ) :
    sec8Ex1Approx 0 N z = 1 := by
  induction N with
  | zero => simp [sec8Ex1Approx, sec8Ex1Coeff]
  | succ N ih =>
      rw [sec8Ex1Approx, Finset.sum_range_succ, ← sec8Ex1Approx, ih]
      simp [sec8Ex1Coeff]

private lemma sec8Ex1_norm_recip_le (z : ℂ) (hre : 0 ≤ z.re) (hnorm : 1 ≤ ‖z‖)
    (k : ℕ) : ‖sec8Ex1Recip (k + 1) z‖ ≤ 1 / ‖z‖ := by
  have hpow : ‖z‖ ≤ ‖z‖ ^ (k + 1) := by
    have h := pow_le_pow_right₀ hnorm (show 1 ≤ k + 1 by omega)
    simpa using h
  have hprod : ‖z‖ ≤ ‖sec8Ex1Prod (k + 1) z‖ :=
    hpow.trans (sec8Ex1_pow_norm_le_norm_prod z hre (k + 1))
  rw [sec8Ex1Recip, norm_div, norm_one]
  exact one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hnorm) hprod

private lemma sec8Ex1_error_succ (k N : ℕ) (z : ℂ) (hre : 0 ≤ z.re)
    (hnorm : 1 ≤ ‖z‖) :
    sec8Ex1Recip (k + 1) z - sec8Ex1Approx (k + 1) (N + 1) z =
      (sec8Ex1Recip k z - sec8Ex1Approx k N z) / z -
        (k + 1 : ℂ) *
          (sec8Ex1Recip (k + 1) z - sec8Ex1Approx (k + 1) N z) / z := by
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hnorm))
  have hp := sec8Ex1Prod_ne_zero z hre hnorm k
  have hfac : z + ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt <| lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hnorm)
      (sec8Ex1_norm_le_norm_add_nat z hre (k + 1))
  conv_lhs =>
    rw [sec8Ex1Recip_succ k z hz hp hfac, sec8Ex1Approx_succ]
  ring

private lemma sec8Ex1_expansion_bound (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → 1 ≤ ‖z‖ →
      ‖sec8Ex1Recip k z - sec8Ex1Approx k N z‖ ≤ C / ‖z‖ ^ (N + 1) := by
  induction N generalizing k with
  | zero =>
      cases k with
      | zero =>
          refine ⟨0, le_rfl, fun z hre hnorm => ?_⟩
          simp [sec8Ex1Recip, sec8Ex1Prod, sec8Ex1Approx_zero]
      | succ k =>
          refine ⟨1, zero_le_one, fun z hre hnorm => ?_⟩
          rw [sec8Ex1Approx_zero_succ, sub_zero]
          simpa only [zero_add, pow_one] using sec8Ex1_norm_recip_le z hre hnorm k
  | succ N ih =>
      cases k with
      | zero =>
          refine ⟨0, le_rfl, fun z hre hnorm => ?_⟩
          simp [sec8Ex1Recip, sec8Ex1Prod, sec8Ex1Approx_zero]
      | succ k =>
          obtain ⟨C₁, hC₁, h₁⟩ := ih k
          obtain ⟨C₂, hC₂, h₂⟩ := ih (k + 1)
          refine ⟨C₁ + (k + 1 : ℝ) * C₂, by positivity, fun z hre hnorm => ?_⟩
          have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hnorm
          have hkNorm : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
            rw [show (k + 1 : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) by norm_num,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
            positivity
          rw [sec8Ex1_error_succ k N z hre hnorm]
          calc
            ‖(sec8Ex1Recip k z - sec8Ex1Approx k N z) / z -
                (k + 1 : ℂ) *
                  (sec8Ex1Recip (k + 1) z - sec8Ex1Approx (k + 1) N z) / z‖ ≤
                ‖(sec8Ex1Recip k z - sec8Ex1Approx k N z) / z‖ +
                  ‖(k + 1 : ℂ) *
                    (sec8Ex1Recip (k + 1) z - sec8Ex1Approx (k + 1) N z) / z‖ :=
              norm_sub_le _ _
            _ = ‖sec8Ex1Recip k z - sec8Ex1Approx k N z‖ / ‖z‖ +
                (k + 1 : ℝ) *
                  ‖sec8Ex1Recip (k + 1) z - sec8Ex1Approx (k + 1) N z‖ / ‖z‖ := by
              simp only [norm_div, norm_mul, hkNorm]
            _ ≤ (C₁ / ‖z‖ ^ (N + 1)) / ‖z‖ +
                (k + 1 : ℝ) * (C₂ / ‖z‖ ^ (N + 1)) / ‖z‖ := by
              apply add_le_add
              · exact div_le_div_of_nonneg_right (h₁ z hre hnorm) (norm_nonneg z)
              · exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (h₂ z hre hnorm) (by positivity))
                  (norm_nonneg z)
            _ = (C₁ + (k + 1 : ℝ) * C₂) / ‖z‖ ^ (N + 1 + 1) := by
              rw [pow_succ]
              field_simp
              ring

private lemma sec8Ex1_finite_part_bound (a : ℕ → ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → 1 ≤ ‖z‖ →
      ‖(∑ j ∈ Finset.range (N + 1), sec8Ex1Term a j z) - sec8Ex1Main a N z‖ ≤
        C / ‖z‖ ^ (N + 2) := by
  choose C hC hbound using fun j : ℕ => sec8Ex1_expansion_bound (N + 1) (j + 1)
  refine ⟨∑ j ∈ Finset.range (N + 1), ‖a j‖ * C j,
    Finset.sum_nonneg fun j hj => mul_nonneg (norm_nonneg _) (hC j), ?_⟩
  intro z hre hnorm
  rw [← sec8Ex1FiniteApprox_eq_main]
  have hsum :
      (∑ j ∈ Finset.range (N + 1), sec8Ex1Term a j z) -
          sec8Ex1FiniteApprox a N z =
        ∑ j ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ j * a j *
            (sec8Ex1Recip (j + 1) z - sec8Ex1Approx (j + 1) (N + 1) z) := by
    rw [sec8Ex1FiniteApprox, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [sec8Ex1Term, sec8Ex1Recip]
    ring
  rw [hsum]
  calc
    ‖∑ j ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ j * a j *
          (sec8Ex1Recip (j + 1) z - sec8Ex1Approx (j + 1) (N + 1) z)‖ ≤
        ∑ j ∈ Finset.range (N + 1),
          ‖(-1 : ℂ) ^ j * a j *
            (sec8Ex1Recip (j + 1) z - sec8Ex1Approx (j + 1) (N + 1) z)‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (N + 1),
        ‖a j‖ * ‖sec8Ex1Recip (j + 1) z - sec8Ex1Approx (j + 1) (N + 1) z‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ ≤ ∑ j ∈ Finset.range (N + 1), ‖a j‖ * (C j / ‖z‖ ^ (N + 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hbound j z hre hnorm) (norm_nonneg _)
    _ = (∑ j ∈ Finset.range (N + 1), ‖a j‖ * C j) / ‖z‖ ^ (N + 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private lemma sec8Ex1RealProd_pos {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    0 < sec8Ex1RealProd x j := by
  apply Finset.prod_pos
  intro k hk
  simp only [Finset.mem_range] at hk ⊢
  positivity

private lemma sec8Ex1_norm_prod_ofReal {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ‖sec8Ex1Prod (j + 1) (x : ℂ)‖ = sec8Ex1RealProd x j := by
  rw [sec8Ex1Prod, sec8Ex1RealProd, norm_prod]
  apply Finset.prod_congr rfl
  intro k hk
  have hcast : (x : ℂ) + ((k + 1 : ℕ) : ℂ) =
      ((x + ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by norm_num
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

private lemma sec8Ex1_norm_term_ofReal (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ‖sec8Ex1Term a j (x : ℂ)‖ = ‖a j‖ / sec8Ex1RealProd x j := by
  rw [sec8Ex1Term, norm_div, norm_mul, sec8Ex1_norm_prod_ofReal hx]
  simp

private lemma sec8Ex1RealProd_shift_two (x : ℝ) (j : ℕ) :
    sec8Ex1RealProd x j *
        (x + ((j + 2 : ℕ) : ℝ)) * (x + ((j + 3 : ℕ) : ℝ)) =
      (x + 1) * (x + 2) * sec8Ex1RealProd (x + 2) j := by
  induction j with
  | zero =>
      simp only [sec8Ex1RealProd, Finset.prod_range_succ, Finset.prod_range_zero]
      ring
  | succ j ih =>
      rw [sec8Ex1RealProd_succ, sec8Ex1RealProd_succ]
      push_cast at ih ⊢
      convert congrArg (fun t : ℝ => t * (x + (j : ℝ) + 4)) ih using 1 <;> ring

private lemma sec8Ex1_norm_ratio (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ‖a j‖ / sec8Ex1RealProd (x + 2) j =
      (‖a j‖ / sec8Ex1RealProd x j) * ((x + 1) * (x + 2)) /
        ((x + ((j + 2 : ℕ) : ℝ)) * (x + ((j + 3 : ℕ) : ℝ))) := by
  have hp : sec8Ex1RealProd x j ≠ 0 := ne_of_gt (sec8Ex1RealProd_pos hx j)
  have hp' : sec8Ex1RealProd (x + 2) j ≠ 0 := by
    apply ne_of_gt
    apply sec8Ex1RealProd_pos
    positivity
  have h₂ : x + ((j + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h₃ : x + ((j + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  convert congrArg (fun t : ℝ => ‖a j‖ * t) (sec8Ex1RealProd_shift_two x j) using 1 <;>
    ring

private lemma sec8Ex1_summable_inv_sq :
    Summable (fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h

private lemma sec8Ex1_reference_summable (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (hconv : Summable (fun j : ℕ => sec8Ex1Term a j (x : ℂ))) :
    Summable (fun j : ℕ => ‖a j‖ / sec8Ex1RealProd (x + 2) j) := by
  have hb := Metric.isBounded_range_of_tendsto _ hconv.tendsto_atTop_zero
  rw [Metric.isBounded_iff_subset_closedBall 0] at hb
  obtain ⟨M, hM⟩ := hb
  have hterm (j : ℕ) : ‖sec8Ex1Term a j (x : ℂ)‖ ≤ |M| := by
    have hj := Metric.mem_closedBall.mp (hM (Set.mem_range_self j))
    have hj' : ‖sec8Ex1Term a j (x : ℂ)‖ ≤ M := by
      simpa only [dist_zero_right] using hj
    exact hj'.trans (le_abs_self M)
  let K : ℝ := |M| * (x + 1) * (x + 2)
  have hmajor : Summable (fun j : ℕ => K * (1 / (((j : ℝ) + 1) ^ 2))) :=
    sec8Ex1_summable_inv_sq.mul_left K
  refine Summable.of_nonneg_of_le
    (f := fun j : ℕ => K * (1 / (((j : ℝ) + 1) ^ 2)))
    (g := fun j : ℕ => ‖a j‖ / sec8Ex1RealProd (x + 2) j) ?_ ?_ hmajor
  · intro j
    exact div_nonneg (norm_nonneg _) (sec8Ex1RealProd_pos (by positivity) j).le
  · intro j
    rw [sec8Ex1_norm_ratio a hx j, ← sec8Ex1_norm_term_ofReal a hx j]
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hden : ((j : ℝ) + 1) ^ 2 ≤
        (x + ((j + 2 : ℕ) : ℝ)) * (x + ((j + 3 : ℕ) : ℝ)) := by
      push_cast
      nlinarith
    have hden_pos : 0 <
        (x + ((j + 2 : ℕ) : ℝ)) * (x + ((j + 3 : ℕ) : ℝ)) := by positivity
    have hsq_pos : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
    have hnum : ‖sec8Ex1Term a j (x : ℂ)‖ * ((x + 1) * (x + 2)) ≤ K := by
      dsimp [K]
      have hx12 : 0 ≤ (x + 1) * (x + 2) := by positivity
      nlinarith [hterm j]
    calc
      ‖sec8Ex1Term a j (x : ℂ)‖ * ((x + 1) * (x + 2)) /
          ((x + ((j + 2 : ℕ) : ℝ)) * (x + ((j + 3 : ℕ) : ℝ))) ≤
          K / ((x + ((j + 2 : ℕ) : ℝ)) * (x + ((j + 3 : ℕ) : ℝ))) :=
            div_le_div_of_nonneg_right hnum hden_pos.le
      _ ≤ K / (((j : ℝ) + 1) ^ 2) :=
        div_le_div_of_nonneg_left (by dsimp [K]; positivity) hsq_pos hden
      _ = K * (1 / (((j : ℝ) + 1) ^ 2)) := by ring

private lemma sec8Ex1_real_factor_le_norm {x : ℝ} {z : ℂ} (hz : x ≤ z.re) (m : ℕ) :
    x + (m : ℝ) ≤ ‖z + (m : ℂ)‖ := by
  calc
    x + (m : ℝ) ≤ z.re + (m : ℝ) := by linarith
    _ = (z + (m : ℂ)).re := by simp
    _ ≤ ‖z + (m : ℂ)‖ := Complex.re_le_norm _

private lemma sec8Ex1RealProd_split (x : ℝ) (N n : ℕ) :
    sec8Ex1RealProd x (n + (N + 1)) = sec8Ex1RealProd x (N + 1) *
      ∏ i ∈ Finset.range n, (x + ((N + 2 + i + 1 : ℕ) : ℝ)) := by
  rw [sec8Ex1RealProd, sec8Ex1RealProd,
    show n + (N + 1) + 1 = (N + 2) + n by omega, Finset.prod_range_add]

private lemma sec8Ex1_tail_prod_lower {x : ℝ} {z : ℂ} (hx : 0 ≤ x) (hz : x ≤ z.re)
    (N n : ℕ) :
    ‖z‖ ^ (N + 2) *
        (∏ i ∈ Finset.range n, (x + ((N + 2 + i + 1 : ℕ) : ℝ))) ≤
      ‖sec8Ex1Prod (n + (N + 1) + 1) z‖ := by
  have hre : 0 ≤ z.re := hx.trans hz
  rw [show n + (N + 1) + 1 = (N + 2) + n by omega, sec8Ex1Prod_split,
    norm_mul, norm_prod]
  apply mul_le_mul (sec8Ex1_pow_norm_le_norm_prod z hre (N + 2))
  · apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact sec8Ex1_real_factor_le_norm hz (N + 2 + i + 1)
  · apply Finset.prod_nonneg
    intro i hi
    positivity
  · exact norm_nonneg _

private lemma sec8Ex1_tail_term_le (a : ℕ → ℂ) {x : ℝ} {z : ℂ} (hx : 0 ≤ x)
    (hz : x ≤ z.re) (hnorm : 1 ≤ ‖z‖) (N n : ℕ) :
    ‖sec8Ex1Term a (n + (N + 1)) z‖ ≤
      sec8Ex1RealProd x (N + 1) *
        (‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1))) /
          ‖z‖ ^ (N + 2) := by
  let T : ℝ := ∏ i ∈ Finset.range n, (x + ((N + 2 + i + 1 : ℕ) : ℝ))
  let D : ℝ := sec8Ex1RealProd x (N + 1)
  have hTpos : 0 < T := by
    apply Finset.prod_pos
    intro i hi
    positivity
  have hDpos : 0 < D := by
    exact sec8Ex1RealProd_pos hx (N + 1)
  have hreal : sec8Ex1RealProd x (n + (N + 1)) = D * T := by
    exact sec8Ex1RealProd_split x N n
  have hpowpos : 0 < ‖z‖ ^ (N + 2) := pow_pos (lt_of_lt_of_le zero_lt_one hnorm) _
  have hlower : ‖z‖ ^ (N + 2) * T ≤
      ‖sec8Ex1Prod (n + (N + 1) + 1) z‖ :=
    sec8Ex1_tail_prod_lower hx hz N n
  rw [sec8Ex1Term, norm_div, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    ‖a (n + (N + 1))‖ / ‖sec8Ex1Prod (n + (N + 1) + 1) z‖ ≤
        ‖a (n + (N + 1))‖ / (‖z‖ ^ (N + 2) * T) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hpowpos hTpos) hlower
    _ = D * (‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1))) /
        ‖z‖ ^ (N + 2) := by
      rw [hreal]
      field_simp

private lemma sec8Ex1_tail_bound (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (hq : Summable (fun j : ℕ => ‖a j‖ / sec8Ex1RealProd x j)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, x ≤ z.re → 1 ≤ ‖z‖ →
      ‖∑' n : ℕ, sec8Ex1Term a (n + (N + 1)) z‖ ≤ C / ‖z‖ ^ (N + 2) := by
  have hshift : Summable (fun n : ℕ =>
      ‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1))) :=
    hq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  let D : ℝ := sec8Ex1RealProd x (N + 1)
  let S : ℝ := ∑' n : ℕ,
    ‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1))
  have hS : 0 ≤ S := by
    apply tsum_nonneg
    intro n
    exact div_nonneg (norm_nonneg _) (sec8Ex1RealProd_pos hx _).le
  have hD : 0 ≤ D := (sec8Ex1RealProd_pos hx _).le
  refine ⟨D * S, mul_nonneg hD hS, ?_⟩
  intro z hz hnorm
  let K : ℝ := D / ‖z‖ ^ (N + 2)
  have hK : 0 ≤ K := div_nonneg hD (pow_nonneg (norm_nonneg z) _)
  have hmajor : Summable (fun n : ℕ => K *
      (‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1)))) :=
    hshift.mul_left K
  have hterm (n : ℕ) : ‖sec8Ex1Term a (n + (N + 1)) z‖ ≤ K *
      (‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1))) := by
    dsimp [K, D]
    convert sec8Ex1_tail_term_le a hx hz hnorm N n using 1
    all_goals ring
  have habs : Summable (fun n : ℕ => ‖sec8Ex1Term a (n + (N + 1)) z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmajor
  calc
    ‖∑' n : ℕ, sec8Ex1Term a (n + (N + 1)) z‖ ≤
        ∑' n : ℕ, ‖sec8Ex1Term a (n + (N + 1)) z‖ :=
      norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n : ℕ, K *
        (‖a (n + (N + 1))‖ / sec8Ex1RealProd x (n + (N + 1))) :=
      Summable.tsum_le_tsum hterm habs hmajor
    _ = K * S := by
      rw [hshift.tsum_mul_left]
    _ = D * S / ‖z‖ ^ (N + 2) := by
      dsimp [K]
      ring

private lemma sec8Ex1_sector_re_lower {eps : ℝ} (heps : 0 < eps)
    (heps_lt : eps < Real.pi / 2) (w : ℂ)
    (harg : |Complex.arg w| ≤ Real.pi / 2 - eps) :
    Real.sin eps * ‖w‖ ≤ w.re := by
  have hupper : Real.pi / 2 - eps ≤ Real.pi := by
    have hpi := Real.pi_pos
    linarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Complex.arg w))
    hupper harg
  rw [Real.cos_pi_div_two_sub, Real.cos_abs] at hcos
  calc
    Real.sin eps * ‖w‖ = ‖w‖ * Real.sin eps := by ring
    _ ≤ ‖w‖ * Real.cos (Complex.arg w) :=
      mul_le_mul_of_nonneg_left hcos (norm_nonneg w)
    _ = w.re := Complex.norm_mul_cos_arg w

private lemma sec8Ex1_sector_radius (x eps r : ℝ) (hx : 0 ≤ x) (heps : 0 < eps)
    (heps_lt : eps < Real.pi / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ,
      |Complex.arg (z - (r : ℂ))| ≤ Real.pi / 2 - eps → R ≤ ‖z‖ →
        x ≤ z.re ∧ 1 ≤ ‖z‖ := by
  let d : ℝ := Real.sin eps
  have heps_pi : eps < Real.pi := by
    have hpi := Real.pi_pos
    linarith
  have hd : 0 < d := Real.sin_pos_of_pos_of_lt_pi heps heps_pi
  let R : ℝ := |r| + (x + |r| + 1) / d + 1
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRone : 1 ≤ R := by
    have hq : 0 ≤ (x + |r| + 1) / d := by positivity
    dsimp [R]
    linarith [abs_nonneg r]
  refine ⟨R, hRpos, ?_⟩
  intro z harg hR
  have htri : ‖z‖ ≤ ‖z - (r : ℂ)‖ + |r| := by
    calc
      ‖z‖ = ‖(z - (r : ℂ)) + (r : ℂ)‖ := by
        congr 1
        ring
      _ ≤ ‖z - (r : ℂ)‖ + ‖(r : ℂ)‖ := norm_add_le _ _
      _ = ‖z - (r : ℂ)‖ + |r| := by simp
  have hw : (x + |r| + 1) / d + 1 ≤ ‖z - (r : ℂ)‖ := by
    dsimp [R] at hR
    linarith
  have hlower := sec8Ex1_sector_re_lower heps heps_lt (z - (r : ℂ)) harg
  have hmul := mul_le_mul_of_nonneg_left hw hd.le
  have hdiv : d * ((x + |r| + 1) / d) = x + |r| + 1 := by
    field_simp
  have hre : (z - (r : ℂ)).re = z.re - r := by simp
  rw [hre] at hlower
  constructor
  · nlinarith [neg_le_abs r]
  · exact hRone.trans hR

private lemma sec8Ex1_asymptotic (a : ℕ → ℂ) (ψ : ℂ → ℂ) (x₁ r eps : ℝ)
    (hx₁ : 0 ≤ x₁) (heps : 0 < eps) (heps_lt : eps < Real.pi / 2)
    (href : Summable (fun j : ℕ => sec8Ex1Term a j (x₁ : ℂ))) :
    ∀ N : ℕ, ∃ C : ℝ, ∃ R : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ z : ℂ,
      HasSum (fun j : ℕ => sec8Ex1Term a j z) (ψ z) →
      |Complex.arg (z - (r : ℂ))| ≤ Real.pi / 2 - eps → R ≤ ‖z‖ →
        ‖ψ z - sec8Ex1Main a N z‖ ≤ C / ‖z‖ ^ (N + 2) := by
  have hq := sec8Ex1_reference_summable a hx₁ href
  intro N
  obtain ⟨Cfin, hCfin, hfin⟩ := sec8Ex1_finite_part_bound a N
  obtain ⟨Ctail, hCtail, htail⟩ := sec8Ex1_tail_bound a (by positivity) hq N
  obtain ⟨R, hR, hsector⟩ := sec8Ex1_sector_radius (x₁ + 2) eps r (by positivity)
    heps heps_lt
  refine ⟨Cfin + Ctail, R, hR, add_nonneg hCfin hCtail, ?_⟩
  intro z hsum harg hnorm
  obtain ⟨hre, hnorm_one⟩ := hsector z harg hnorm
  have hre0 : 0 ≤ z.re := (by positivity : 0 ≤ x₁ + 2).trans hre
  have hfinz := hfin z hre0 hnorm_one
  have htailz := htail z hre hnorm_one
  have hsplit := hsum.summable.sum_add_tsum_nat_add (N + 1)
  have hpsi : ψ z = (∑ j ∈ Finset.range (N + 1), sec8Ex1Term a j z) +
      ∑' n : ℕ, sec8Ex1Term a (n + (N + 1)) z := by
    rw [hsum.tsum_eq] at hsplit
    exact hsplit.symm
  rw [hpsi]
  calc
    ‖(∑ j ∈ Finset.range (N + 1), sec8Ex1Term a j z) +
          (∑' n : ℕ, sec8Ex1Term a (n + (N + 1)) z) - sec8Ex1Main a N z‖ =
        ‖((∑ j ∈ Finset.range (N + 1), sec8Ex1Term a j z) - sec8Ex1Main a N z) +
          ∑' n : ℕ, sec8Ex1Term a (n + (N + 1)) z‖ := by ring_nf
    _ ≤ ‖(∑ j ∈ Finset.range (N + 1), sec8Ex1Term a j z) - sec8Ex1Main a N z‖ +
        ‖∑' n : ℕ, sec8Ex1Term a (n + (N + 1)) z‖ := norm_add_le _ _
    _ ≤ Cfin / ‖z‖ ^ (N + 2) + Ctail / ‖z‖ ^ (N + 2) :=
      add_le_add hfinz htailz
    _ = (Cfin + Ctail) / ‖z‖ ^ (N + 2) := by ring

/-- **Asymptotic expansion of a factorial series.** Let $a_0, a_1, \ldots$ be complex numbers, let
$\psi : \mathbb{C} \to \mathbb{C}$, let $\lambda$ be either a real number or $-\infty$, and let
$0 < \varepsilon < \pi/2$. Suppose that for every complex $z$ that is not a negative integer and
satisfies $\operatorname{Re} z > \lambda$, the series
$$\sum_{j=0}^{\infty} \frac{(-1)^j a_j}{(z + 1)(z + 2) \cdots (z + j + 1)}$$
converges absolutely with sum $\psi(z)$. Write $S(n, k)$ for the Stirling numbers of the second
kind and $c_j = \sum_{k=0}^{j} a_k S(j + 1, k + 1)$. Then for every natural number $N$ there are
real numbers $C \ge 0$ and $R > 0$ such that
$$\Big|\psi(z) - \sum_{j=0}^{N} \frac{(-1)^j c_j}{z^{j+1}}\Big| \le \frac{C}{|z|^{N+2}}$$
for every complex $z$ that is not a negative integer, satisfies $\operatorname{Re} z > \lambda$
and $|z| \ge R$, and lies in the sector $|\arg z| \le \pi/2 - \varepsilon$ when
$\lambda = -\infty$, or $|\arg(z - \lambda)| \le \pi/2 - \varepsilon$ when $\lambda$ is real.

For $\lambda = -\infty$ the expansion is stated on the sector $|\arg z| \le \pi/2 - \varepsilon$,
as for real $\lambda$; on the wider sector $|\arg z| \le \pi - \varepsilon$ it fails, for example
for $a_j = j!\,(-2/3)^j$.

Proof: Use convergence at one real point to obtain absolute convergence two units to the right,
then expand each $1/((z + 1)\cdots(z + j + 1))$ termwise in powers of $1/z$ and bound the tail.

Proves `Wanted` entry `ramanujan_part1_ch3_section8_example1_asymptotic`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 1, formula
    (8.1), printed p. 50 / PDF p. 60.
-/
theorem ramanujan_part1_ch3_section8_example1_asymptotic
  (a : ℕ → ℂ)
  (ψ : ℂ → ℂ)
  (lam : WithBot ℝ)
  (eps : ℝ)
  (heps_pos : 0 < eps)
  (heps_lt_pi_div_two : lam ≠ (⊥ : WithBot ℝ) → eps < Real.pi / 2)
  (heps_lt_pi_div_two_bot : lam = (⊥ : WithBot ℝ) → eps < Real.pi / 2)
  (hsum : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) → lam < (↑z.re : WithBot ℝ) →
      HasSum (fun j : ℕ => (-1 : ℂ) ^ j * a j / ∏ k ∈ Finset.range (j + 1), (z + ((k + 1 : ℕ) : ℂ)))
          (ψ z)) :
    ∀ N : ℕ, ∃ C : ℝ, ∃ R : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
        lam < (↑z.re : WithBot ℝ) →
            ((lam = (⊥ : WithBot ℝ) → |Complex.arg z| ≤ Real.pi / 2 - eps) ∧
                (∀ r : ℝ, lam = (↑r : WithBot ℝ) → |Complex.arg (z - (r : ℂ))| ≤ Real.pi /
                    2 - eps)) →
                R ≤ ‖z‖ → ‖ψ z - ∑ j ∈ Finset.range (N + 1),
                    ((-1 : ℂ) ^ j *
                        (∑ k ∈ Finset.range (j + 1), a k *
                            ((Nat.stirlingSecond (j + 1) (k + 1) : ℕ) : ℂ)) / z ^ (j + 1))‖ ≤ C /
                            ‖z‖ ^ (N + 2) := by
  induction lam with
  | bot =>
      have hpole : ∀ n : ℕ, (0 : ℂ) ≠ -((n + 1 : ℕ) : ℂ) := by
        intro n hn
        have hre := congrArg Complex.re hn
        simp at hre
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have href : Summable (fun j : ℕ => sec8Ex1Term a j (0 : ℂ)) := by
        have h := (hsum 0 hpole (by simp)).summable
        simpa only [sec8Ex1Term, sec8Ex1Prod] using h
      have hcore := sec8Ex1_asymptotic a ψ 0 0 eps (by norm_num) heps_pos
        (heps_lt_pi_div_two_bot rfl) href
      intro N
      obtain ⟨C, R, hR, hC, hbound⟩ := hcore N
      refine ⟨C, R, hR, hC, ?_⟩
      intro z hpolez hlam hsector hnorm
      have hsumz : HasSum (fun j : ℕ => sec8Ex1Term a j z) (ψ z) := by
        simpa only [sec8Ex1Term, sec8Ex1Prod] using hsum z hpolez hlam
      have harg : |Complex.arg (z - (0 : ℂ))| ≤ Real.pi / 2 - eps := by
        simpa using hsector.1 rfl
      simpa only [sec8Ex1Main] using hbound z hsumz harg hnorm
  | coe r =>
      let x₁ : ℝ := max r 0 + 1
      have hx₁ : 0 ≤ x₁ := by
        dsimp [x₁]
        linarith [le_max_right r 0]
      have hrx₁ : r < x₁ := by
        dsimp [x₁]
        linarith [le_max_left r 0]
      have hpole : ∀ n : ℕ, (x₁ : ℂ) ≠ -((n + 1 : ℕ) : ℂ) := by
        intro n hn
        have hre := congrArg Complex.re hn
        have hx₁pos : 0 < x₁ := lt_of_lt_of_le zero_lt_one (by
          dsimp [x₁]
          linarith [le_max_right r 0])
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
        have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        linarith
      have href : Summable (fun j : ℕ => sec8Ex1Term a j (x₁ : ℂ)) := by
        have hlt : (↑r : WithBot ℝ) < (↑x₁ : WithBot ℝ) := by simpa using hrx₁
        have h := (hsum (x₁ : ℂ) hpole hlt).summable
        simpa only [sec8Ex1Term, sec8Ex1Prod] using h
      have hcore := sec8Ex1_asymptotic a ψ x₁ r eps hx₁ heps_pos
        (heps_lt_pi_div_two (by simp)) href
      intro N
      obtain ⟨C, R, hR, hC, hbound⟩ := hcore N
      refine ⟨C, R, hR, hC, ?_⟩
      intro z hpolez hlam hsector hnorm
      have hsumz : HasSum (fun j : ℕ => sec8Ex1Term a j z) (ψ z) := by
        simpa only [sec8Ex1Term, sec8Ex1Prod] using hsum z hpolez hlam
      have harg : |Complex.arg (z - (r : ℂ))| ≤ Real.pi / 2 - eps :=
        hsector.2 r rfl
      simpa only [sec8Ex1Main] using hbound z hsumz harg hnorm

end Section8Example1Asymptotic

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
