/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry34Zeta3doublesum

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)

noncomputable section

def chapter9Entry34LeftTerm (x : ℝ) (k : ℕ) : ℝ :=
  (x / (1 + x)) ^ (k + 1) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def chapter9Entry34RightTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 *
      chapter9OddHarmonic (k + 1) * x ^ (k + 1) /
    ((2 * k + 1).factorial : ℝ)

private lemma chapter9OddHarmonic_nonneg (n : ℕ) :
    0 ≤ chapter9OddHarmonic n := by
  unfold chapter9OddHarmonic
  apply Finset.sum_nonneg
  intro j _
  positivity

private lemma chapter9OddHarmonic_le (n : ℕ) :
    chapter9OddHarmonic n ≤ (n : ℝ) := by
  unfold chapter9OddHarmonic
  calc ∑ j ∈ range n, 1 / ((2 * j + 1 : ℕ) : ℝ)
      ≤ ∑ _j ∈ range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_left 1 (2 * j)
        have hpos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by linarith
        exact (div_le_one hpos).mpr h1
    _ = (n : ℝ) := by simp

private lemma chapter9centralRatio_le_fact (k : ℕ) :
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ)) ^ 2 ≤
      (((2 * k + 1).factorial : ℕ) : ℝ) := by
  have hnat : ∀ k : ℕ, 2 ^ (2 * k) * k.factorial * k.factorial ≤
      (2 * k + 1).factorial := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hexp : 2 * (k + 1) = 2 * k + 2 := by omega
      have eL : (2 : ℕ) ^ (2 * (k + 1)) * (k + 1).factorial * (k + 1).factorial
          = (2 ^ (2 * k) * k.factorial * k.factorial) *
            (2 ^ 2 * (k + 1) * (k + 1)) := by
        rw [hexp, pow_add, Nat.factorial_succ]; ring
      have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      have eR : (2 * (k + 1) + 1).factorial
          = ((2 * k + 1).factorial) * ((2 * (k + 1) + 1) * (2 * (k + 1))) := by
        rw [Nat.factorial_succ, h2, Nat.factorial_succ]; ring
      rw [eL, eR]
      have hle2 : 2 ^ 2 * (k + 1) * (k + 1)
          ≤ (2 * (k + 1) + 1) * (2 * (k + 1)) := by
        calc 2 ^ 2 * (k + 1) * (k + 1)
            = 4 * ((k + 1) * (k + 1)) := by ring
          _ ≤ 4 * ((k + 1) * (k + 1)) + 2 * (k + 1) :=
              Nat.le_add_right _ _
          _ = (2 * (k + 1) + 1) * (2 * (k + 1)) := by ring
      exact mul_le_mul ih hle2 (Nat.zero_le _) (Nat.zero_le _)
  have hle := hnat k
  have hR : (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (k.factorial : ℝ) ≤
      ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hle
  calc (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ)) ^ 2
      = (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (k.factorial : ℝ) := by ring
    _ ≤ ((((2 * k + 1).factorial : ℕ)) : ℝ) := hR

private lemma summable_chapter9Entry34LeftTerm (x : ℝ)
    (hx : |x / (1 + x)| < 1) :
    Summable (chapter9Entry34LeftTerm x) := by
  have hnorm : ‖|x / (1 + x)|‖ < 1 := by rw [Real.norm_eq_abs, abs_abs]; exact hx
  have hgeo : Summable (fun k : ℕ => |x / (1 + x)| ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one hnorm)
  apply Summable.of_norm_bounded hgeo
  intro k
  unfold chapter9Entry34LeftTerm
  have hb : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 (2 * k)
  have h1 : (1 : ℝ) ≤ (((2 * k + 1 : ℕ) : ℝ) ^ 2) := one_le_pow₀ hb
  have hd0 : (0 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by positivity
  simp only [norm_div, norm_pow, Real.norm_eq_abs, abs_div]
  rw [abs_of_nonneg hd0]
  exact div_le_self (by positivity : (0 : ℝ) ≤ (|x| / |1 + x|) ^ (k + 1)) h1

private lemma summable_chapter9Entry34RightTerm (x : ℝ)
    (hx : |x| < 1) :
    Summable (chapter9Entry34RightTerm x) := by
  have habs1 : ‖|x|‖ < 1 := by rw [Real.norm_eq_abs, abs_abs]; exact hx
  have hpoly : Summable (fun k : ℕ => ((k : ℝ) + 1) * |x| ^ (k + 1)) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * |x| ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 habs1
    have h1' : Summable (fun k : ℕ => (k : ℝ) * |x| ^ k) := by
      simpa using h1
    have h2 : Summable (fun k : ℕ => |x| ^ k) :=
      summable_geometric_of_norm_lt_one habs1
    have h3 := (h1'.add h2).mul_left |x|
    have heq : (fun k : ℕ => ((k : ℝ) + 1) * |x| ^ (k + 1))
        = (fun k : ℕ => |x| * ((k : ℝ) * |x| ^ k + |x| ^ k)) := by
      funext k; ring
    rw [heq]; exact h3
  apply Summable.of_norm_bounded hpoly
  intro k
  have hHnn := chapter9OddHarmonic_nonneg (k + 1)
  have hHle : chapter9OddHarmonic (k + 1) ≤ ((k : ℝ) + 1) := by
    have h := chapter9OddHarmonic_le (k + 1)
    push_cast at h ⊢
    linarith
  have hFpos : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * k + 1)
  have hcle : (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 /
      ((((2 * k + 1).factorial : ℕ)) : ℝ) ≤ 1 := by
    rw [div_le_one hFpos]
    exact chapter9centralRatio_le_fact k
  have e3 : |(((k.factorial : ℕ)) : ℝ)| = (((k.factorial : ℕ)) : ℝ) :=
    abs_of_nonneg (by exact_mod_cast Nat.zero_le (k.factorial))
  have e4 : |chapter9OddHarmonic (k + 1)| = chapter9OddHarmonic (k + 1) :=
    abs_of_nonneg hHnn
  have e6 : |((((2 * k + 1).factorial : ℕ)) : ℝ)| =
      ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
    abs_of_nonneg (by exact_mod_cast Nat.zero_le ((2 * k + 1).factorial))
  unfold chapter9Entry34RightTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_neg, abs_one,
    one_pow, abs_two, e3, e4, e6, one_mul]
  calc (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 *
          chapter9OddHarmonic (k + 1) * |x| ^ (k + 1) /
          ((((2 * k + 1).factorial : ℕ)) : ℝ)
      = ((2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 /
          ((((2 * k + 1).factorial : ℕ)) : ℝ)) *
          (chapter9OddHarmonic (k + 1) * |x| ^ (k + 1)) := by ring
    _ ≤ 1 * (chapter9OddHarmonic (k + 1) * |x| ^ (k + 1)) := by
        apply mul_le_mul_of_nonneg_right hcle
        exact mul_nonneg hHnn (by positivity)
    _ = chapter9OddHarmonic (k + 1) * |x| ^ (k + 1) := by ring
    _ ≤ ((k : ℝ) + 1) * |x| ^ (k + 1) := by
        apply mul_le_mul_of_nonneg_right hHle (by positivity)

private def chapter9Central (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * n) * (n.factorial : ℝ) ^ 2 / ((((2 * n + 1).factorial : ℕ)) : ℝ)

private def chapter9AltOddRecip (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) / ((2 * k + 1 : ℕ) : ℝ)

private def chapter9AltOddRecipSq (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (n.choose k : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private lemma chapter9Central_pos (n : ℕ) : 0 < chapter9Central n := by
  unfold chapter9Central
  apply div_pos _ _ <;> positivity

private lemma chapter9Central_le_one (n : ℕ) : chapter9Central n ≤ 1 := by
  unfold chapter9Central
  have hFpos : (0 : ℝ) < ((((2 * n + 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * n + 1)
  rw [div_le_one hFpos]
  exact chapter9centralRatio_le_fact n

private lemma chapter9Central_zero : chapter9Central 0 = 1 := by
  unfold chapter9Central
  norm_num

private lemma chapter9AltOddRecip_zero : chapter9AltOddRecip 0 = 1 := by
  unfold chapter9AltOddRecip
  rw [Finset.sum_range_succ]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, Nat.choose_self,
    Nat.cast_one, one_mul]
  norm_num

private lemma chapter9S1_term (n k : ℕ) (hk : k ≤ n) :
    (2 * (n : ℝ) + 3)
          * ((-1 : ℝ) ^ k * (((n + 1).choose k : ℕ) : ℝ)
            / (((2 * k + 1 : ℕ)) : ℝ))
      - 2 * ((n : ℝ) + 1)
          * ((-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / (((2 * k + 1 : ℕ)) : ℝ))
      = (-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ) := by
  have hpos : (0 : ℝ) < (((2 * k + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.succ_pos (2 * k)
  have hne : ((((2 * k + 1 : ℕ))) : ℝ) ≠ 0 := ne_of_gt hpos
  have hCnat : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) :=
    Nat.choose_mul_succ_eq n k
  have hC : ((n.choose k : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((((n + 1).choose k : ℕ)) : ℝ) * ((((n + 1 - k : ℕ))) : ℝ) := by
    exact_mod_cast hCnat
  have hsub : ((((n + 1 - k : ℕ))) : ℝ) = (n : ℝ) + 1 - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1)]
    push_cast
    ring
  rw [hsub] at hC
  have h2k1 : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hmain : (2 * (n : ℝ) + 3) * ((((n + 1).choose k : ℕ)) : ℝ)
      - 2 * ((n : ℝ) + 1) * (((n.choose k : ℕ)) : ℝ)
      = ((((n + 1).choose k : ℕ)) : ℝ) * (2 * (k : ℝ) + 1) := by
    linear_combination -2 * hC
  have hLHS :
      (2 * (n : ℝ) + 3)
            * ((-1 : ℝ) ^ k * (((n + 1).choose k : ℕ) : ℝ)
              / (((2 * k + 1 : ℕ)) : ℝ))
        - 2 * ((n : ℝ) + 1)
            * ((-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
              / (((2 * k + 1 : ℕ)) : ℝ))
        = ((-1 : ℝ) ^ k
            * ((2 * (n : ℝ) + 3) * ((((n + 1).choose k : ℕ)) : ℝ)
              - 2 * ((n : ℝ) + 1) * (((n.choose k : ℕ)) : ℝ)))
          / ((((2 * k + 1 : ℕ))) : ℝ) := by
    field_simp
  rw [hLHS, hmain, h2k1]
  field_simp

private lemma chapter9AltBinomSum_zero (m : ℕ) (hm : m ≠ 0) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ k * (m.choose k : ℝ) = 0 := by
  have h := add_pow (-1 : ℝ) 1 m
  simp only [neg_add_cancel, one_pow, mul_one] at h
  rw [zero_pow hm] at h
  exact h.symm

private lemma chapter9AltOddRecip_succ (n : ℕ) :
    chapter9AltOddRecip (n + 1)
      = 2 * (n + 1) / (2 * n + 3) * chapter9AltOddRecip n := by
  have hne : (2 : ℝ) * n + 3 ≠ 0 := by positivity
  have h0 : (2 * (n : ℝ) + 3) * chapter9AltOddRecip (n + 1)
      - 2 * ((n : ℝ) + 1) * chapter9AltOddRecip n = 0 := by
    unfold chapter9AltOddRecip
    have hCtop0 : n.choose (n + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have htop0 : (-1 : ℝ) ^ (n + 1) * ((n.choose (n + 1) : ℕ) : ℝ)
        / ((((2 * (n + 1) + 1 : ℕ))) : ℝ) = 0 := by
      simp only [hCtop0, Nat.cast_zero, mul_zero, zero_div]
    have hext : (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ))
        = ∑ k ∈ Finset.range (n + 1 + 1),
          (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ) := by
      have h := Finset.sum_range_succ
        (fun k => (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
          / ((((2 * k + 1 : ℕ))) : ℝ)) (n + 1)
      simp only [htop0, add_zero] at h
      exact h.symm
    rw [hext, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    have hsum : (∑ k ∈ Finset.range (n + 1 + 1),
          ((2 * (n : ℝ) + 3)
              * ((-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ)
                / ((((2 * k + 1 : ℕ))) : ℝ))
            - 2 * ((n : ℝ) + 1)
              * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
                / ((((2 * k + 1 : ℕ))) : ℝ))))
        = ∑ k ∈ Finset.range (n + 1 + 1),
          (-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      by_cases hkn : k ≤ n
      · exact chapter9S1_term n k hkn
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        simp only [Nat.choose_self, hCtop0, Nat.cast_one, Nat.cast_zero,
          mul_zero, zero_div, mul_one]
        have hpos3 : (0 : ℝ) < 2 * (n : ℝ) + 3 := by positivity
        have hne3 : (2 : ℝ) * n + 3 ≠ 0 := ne_of_gt hpos3
        have h2k : ((((2 * (n + 1) + 1 : ℕ))) : ℝ)
            = 2 * (n : ℝ) + 3 := by
          push_cast
          ring
        rw [h2k]
        field_simp
        ring
    rw [hsum]
    exact chapter9AltBinomSum_zero (n + 1) (by omega)
  have h1 : (2 * (n : ℝ) + 3) * chapter9AltOddRecip (n + 1)
      = 2 * ((n : ℝ) + 1) * chapter9AltOddRecip n := by
    linarith
  field_simp
  linear_combination h1

private lemma chapter9Central_succ (n : ℕ) :
    chapter9Central (n + 1) = 2 * (n + 1) / (2 * n + 3) * chapter9Central n := by
  have hFn : ((n + 1).factorial : ℝ) = (n + 1) * (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ n
  have hF2 : ((2 * (n + 1) + 1).factorial : ℝ)
      = (2 * n + 3) * (2 * n + 2) * (((2 * n + 1).factorial : ℕ) : ℝ) := by
    have e1 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
    have e2 : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    have hnat : (2 * (n + 1) + 1).factorial
        = (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
      rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
      have e3 : 2 * n + 3 = 2 * (n + 1) + 1 := by omega
      rw [e3]
      ring
    exact_mod_cast hnat
  have hexp : (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
    have e : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [e, pow_add]
    ring
  have hFpos : (0 : ℝ) < ((((2 * n + 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * n + 1)
  have hne1 : ((((2 * n + 1).factorial : ℕ)) : ℝ) ≠ 0 := ne_of_gt hFpos
  have hne2 : (2 : ℝ) * n + 3 ≠ 0 := by positivity
  have hne3 : (2 : ℝ) * n + 2 ≠ 0 := by positivity
  unfold chapter9Central
  rw [hFn, hF2, hexp]
  field_simp
  ring

private lemma chapter9AltOddRecip_eq_central (n : ℕ) :
    chapter9AltOddRecip n = chapter9Central n := by
  induction n with
  | zero =>
    rw [chapter9AltOddRecip_zero, chapter9Central_zero]
  | succ n ih =>
    rw [chapter9AltOddRecip_succ, chapter9Central_succ, ih]

private lemma chapter9AltOddRecipSq_zero :
    chapter9AltOddRecipSq 0 = 1 := by
  unfold chapter9AltOddRecipSq
  rw [Finset.sum_range_succ]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    Nat.choose_self, Nat.cast_one, one_mul]
  norm_num

private lemma chapter9OddHarmonic_one : chapter9OddHarmonic 1 = 1 := by
  unfold chapter9OddHarmonic
  rw [Finset.sum_range_succ]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  norm_num

private lemma chapter9OddHarmonic_succ (n : ℕ) :
    chapter9OddHarmonic (n + 2)
      = chapter9OddHarmonic (n + 1)
        + 1 / ((((2 * (n + 1) + 1 : ℕ))) : ℝ) := by
  unfold chapter9OddHarmonic
  have e : n + 2 = (n + 1) + 1 := by omega
  rw [e, Finset.sum_range_succ]

private lemma chapter9CentralHarmonic_succ (n : ℕ) :
    chapter9Central (n + 1) * chapter9OddHarmonic (n + 2)
      = 2 * (n + 1) / (2 * n + 3)
          * (chapter9Central n * chapter9OddHarmonic (n + 1))
        + 2 * (n + 1) / (2 * n + 3) ^ 2 * chapter9Central n := by
  have hne : (2 : ℝ) * n + 3 ≠ 0 := by positivity
  have hC := chapter9Central_succ n
  have hH := chapter9OddHarmonic_succ n
  have enat : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  rw [enat] at hH
  have hcast : ((((2 * n + 3 : ℕ))) : ℝ) = 2 * (n : ℝ) + 3 := by
    push_cast
    ring
  rw [hcast] at hH
  rw [hC, hH]
  field_simp

private lemma chapter9S2_term (n k : ℕ) (hk : k ≤ n) :
    (2 * (n : ℝ) + 3)
          * ((-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
        - 2 * ((n : ℝ) + 1)
          * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
        - 2 * ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)
          * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ))
      = (-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ)
        / (2 * (n : ℝ) + 3) := by
  have hpos : (0 : ℝ) < (((2 * k + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.succ_pos (2 * k)
  have hne : ((((2 * k + 1 : ℕ))) : ℝ) ≠ 0 := ne_of_gt hpos
  have hne3 : (2 : ℝ) * n + 3 ≠ 0 := by positivity
  have hCnat : n.choose k * (n + 1)
      = (n + 1).choose k * (n + 1 - k) :=
    Nat.choose_mul_succ_eq n k
  have hC : ((n.choose k : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((((n + 1).choose k : ℕ)) : ℝ)
        * ((((n + 1 - k : ℕ))) : ℝ) := by
    exact_mod_cast hCnat
  have hsub : ((((n + 1 - k : ℕ))) : ℝ)
      = (n : ℝ) + 1 - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1)]
    push_cast
    ring
  rw [hsub] at hC
  have h2k1 : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hmain : (2 * (n : ℝ) + 3) ^ 2
        * ((((n + 1).choose k : ℕ)) : ℝ)
        - 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3)
          * (((n.choose k : ℕ)) : ℝ)
        - 2 * ((n : ℝ) + 1) * (((n.choose k : ℕ)) : ℝ)
          * (2 * (k : ℝ) + 1)
      = ((((n + 1).choose k : ℕ)) : ℝ) * (2 * (k : ℝ) + 1) ^ 2 := by
    linear_combination -4 * ((n : ℝ) + (k : ℝ) + 2) * hC
  have hLHS :
      (2 * (n : ℝ) + 3)
            * ((-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ)
              / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
          - 2 * ((n : ℝ) + 1)
            * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
              / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
          - 2 * ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)
            * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
              / ((((2 * k + 1 : ℕ))) : ℝ))
        = (-1 : ℝ) ^ k
          * ((2 * (n : ℝ) + 3) ^ 2
            * ((((n + 1).choose k : ℕ)) : ℝ)
            - 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3)
              * (((n.choose k : ℕ)) : ℝ)
            - 2 * ((n : ℝ) + 1) * (((n.choose k : ℕ)) : ℝ)
              * (2 * (k : ℝ) + 1))
          / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3)) := by
    rw [h2k1]
    field_simp
  rw [hLHS, hmain]
  field_simp

private lemma chapter9AltOddRecipSq_succ (n : ℕ) :
    chapter9AltOddRecipSq (n + 1)
      = 2 * (n + 1) / (2 * n + 3) * chapter9AltOddRecipSq n
        + 2 * (n + 1) / (2 * n + 3) ^ 2 * chapter9AltOddRecip n := by
  have hne : (2 : ℝ) * n + 3 ≠ 0 := by positivity
  have h0 : (2 * (n : ℝ) + 3) ^ 2 * chapter9AltOddRecipSq (n + 1)
      - 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3)
        * chapter9AltOddRecipSq n
      - 2 * ((n : ℝ) + 1) * chapter9AltOddRecip n = 0 := by
    unfold chapter9AltOddRecipSq chapter9AltOddRecip
    have hCtop0 : n.choose (n + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have htopS2 : (-1 : ℝ) ^ (n + 1) * ((n.choose (n + 1) : ℕ) : ℝ)
        / ((((2 * (n + 1) + 1 : ℕ))) : ℝ) ^ 2 = 0 := by
      simp only [hCtop0, Nat.cast_zero, mul_zero, zero_div]
    have htopS1 : (-1 : ℝ) ^ (n + 1) * ((n.choose (n + 1) : ℕ) : ℝ)
        / ((((2 * (n + 1) + 1 : ℕ))) : ℝ) = 0 := by
      simp only [hCtop0, Nat.cast_zero, mul_zero, zero_div]
    have hextS2 : (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
        = ∑ k ∈ Finset.range (n + 1 + 1),
          (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2 := by
      have h := Finset.sum_range_succ
        (fun k => (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
          / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2) (n + 1)
      simp only [htopS2, add_zero] at h
      exact h.symm
    have hextS1 : (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ))
        = ∑ k ∈ Finset.range (n + 1 + 1),
          (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
            / ((((2 * k + 1 : ℕ))) : ℝ) := by
      have h := Finset.sum_range_succ
        (fun k => (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
          / ((((2 * k + 1 : ℕ))) : ℝ)) (n + 1)
      simp only [htopS1, add_zero] at h
      exact h.symm
    rw [hextS2, hextS1, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    have hsum : (∑ k ∈ Finset.range (n + 1 + 1),
          (((2 * (n : ℝ) + 3) ^ 2
              * ((-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ)
                / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
            - 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3)
              * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
                / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2))
            - 2 * ((n : ℝ) + 1)
              * ((-1 : ℝ) ^ k * (((n.choose k : ℕ)) : ℝ)
                / ((((2 * k + 1 : ℕ))) : ℝ))))
        = ∑ k ∈ Finset.range (n + 1 + 1),
          (-1 : ℝ) ^ k * ((((n + 1).choose k : ℕ)) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      by_cases hkn : k ≤ n
      · have h := chapter9S2_term n k hkn
        have hne3 : (2 : ℝ) * n + 3 ≠ 0 := by positivity
        field_simp at h ⊢
        linear_combination h
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        simp only [Nat.choose_self, hCtop0, Nat.cast_one, Nat.cast_zero,
          mul_zero, zero_div, mul_one, mul_zero, sub_zero]
        have h2k : ((((2 * (n + 1) + 1 : ℕ))) : ℝ)
            = 2 * (n : ℝ) + 3 := by
          push_cast
          ring
        rw [h2k]
        field_simp
    rw [hsum]
    exact chapter9AltBinomSum_zero (n + 1) (by omega)
  field_simp
  linear_combination h0

private lemma chapter9AltOddRecipSq_eq (n : ℕ) :
    chapter9AltOddRecipSq n
      = chapter9Central n * chapter9OddHarmonic (n + 1) := by
  induction n with
  | zero =>
    rw [chapter9AltOddRecipSq_zero, chapter9Central_zero,
      chapter9OddHarmonic_one, one_mul]
  | succ n ih =>
    rw [chapter9AltOddRecipSq_succ, chapter9CentralHarmonic_succ,
      chapter9AltOddRecip_eq_central, ih]

private lemma chapter9ChooseConv (k n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (((k + i).choose k : ℕ) : ℝ))
      = ((((k + 1 + n).choose (k + 1) : ℕ)) : ℝ) := by
  have hcomm : ∀ i : ℕ, (k + i).choose k = (i + k).choose k := by
    intro i
    rw [Nat.add_comm k i]
  have hsumNat : (∑ i ∈ Finset.range (n + 1), (k + i).choose k)
      = (k + 1 + n).choose (k + 1) := by
    have h1 : (∑ i ∈ Finset.range (n + 1), (k + i).choose k)
        = ∑ i ∈ Finset.range (n + 1), (i + k).choose k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcomm i]
    rw [h1, Nat.sum_range_add_choose]
    have e : n + k + 1 = k + 1 + n := by omega
    rw [e]
  exact_mod_cast hsumNat

private lemma chapter9BinomConv (y : ℝ) (k n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        ((((k + i).choose k : ℕ)) : ℝ) * y ^ i * y ^ (n - i))
      = ((((k + 1 + n).choose (k + 1) : ℕ)) : ℝ) * y ^ n := by
  have hpow : ∀ i ∈ Finset.range (n + 1), y ^ i * y ^ (n - i) = y ^ n := by
    intro i hi
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    have h : i + (n - i) = n := Nat.add_sub_cancel' hi
    rw [← pow_add, h]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((((k + i).choose k : ℕ)) : ℝ) * y ^ i * y ^ (n - i)
        = ((((k + i).choose k : ℕ)) : ℝ) * y ^ n := by
    intro i hi
    rw [mul_assoc, hpow i hi]
  calc (∑ i ∈ Finset.range (n + 1),
          ((((k + i).choose k : ℕ)) : ℝ) * y ^ i * y ^ (n - i))
      = ∑ i ∈ Finset.range (n + 1),
          ((((k + i).choose k : ℕ)) : ℝ) * y ^ n := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i hi
    _ = (∑ i ∈ Finset.range (n + 1),
          ((((k + i).choose k : ℕ)) : ℝ)) * y ^ n := by
        rw [Finset.sum_mul]
    _ = ((((k + 1 + n).choose (k + 1) : ℕ)) : ℝ) * y ^ n := by
        rw [chapter9ChooseConv]

private lemma chapter9GeomSummableNorm (y : ℝ) (hy : ‖y‖ < 1) :
    Summable (fun j : ℕ => ‖y ^ j‖) := by
  have hnorm : ‖‖y‖‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
    exact hy
  have hgeo : Summable (fun j : ℕ => ‖y‖ ^ j) :=
    summable_geometric_of_norm_lt_one hnorm
  apply hgeo.congr
  intro j
  rw [norm_pow]

private lemma chapter9BinomSummableNorm (y : ℝ) (hy : ‖y‖ < 1) (k : ℕ) :
    Summable (fun j : ℕ => ‖((((k + j).choose k : ℕ)) : ℝ) * y ^ j‖) := by
  induction k with
  | zero =>
    have hgeo := chapter9GeomSummableNorm y hy
    apply hgeo.congr
    intro j
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
  | succ k ih =>
    have hg := chapter9GeomSummableNorm y hy
    have hconv := summable_norm_sum_mul_range_of_summable_norm
      (f := fun j : ℕ => ((((k + j).choose k : ℕ)) : ℝ) * y ^ j)
      (g := fun j : ℕ => y ^ j) ih hg
    apply hconv.congr
    intro n
    congr 1
    have h := chapter9BinomConv y k n
    have e : k + 1 + n = (k + 1) + n := by omega
    rw [e] at h
    exact h

private lemma chapter9LeftWeight_le_one (k : ℕ) :
    (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 (2 * k)
  have hb : (1 : ℝ) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := one_le_pow₀ h1
  have hpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  rw [div_le_one hpos]
  exact hb

private lemma chapter9BinomHasSum (y : ℝ) (hy : ‖y‖ < 1) (k : ℕ) :
    HasSum (fun j : ℕ => ((((k + j).choose k : ℕ)) : ℝ) * y ^ j)
      (((1 - y) ^ (k + 1))⁻¹) := by
  induction k with
  | zero =>
    have hgeo : HasSum (fun j : ℕ => y ^ j) (1 - y)⁻¹ :=
      hasSum_geometric_of_norm_lt_one hy
    have heq : ∀ j : ℕ,
        ((((0 + j).choose 0 : ℕ)) : ℝ) * y ^ j = y ^ j := by
      intro j
      simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have h0 : HasSum (fun j : ℕ => ((((0 + j).choose 0 : ℕ)) : ℝ) * y ^ j)
        (1 - y)⁻¹ := by
      apply hgeo.congr_fun
      intro j
      exact heq j
    simp only [Nat.zero_add, pow_one] at h0 ⊢
    exact h0
  | succ k ih =>
    have hg : HasSum (fun j : ℕ => y ^ j) (1 - y)⁻¹ :=
      hasSum_geometric_of_norm_lt_one hy
    have hfN := chapter9BinomSummableNorm y hy k
    have hgN := chapter9GeomSummableNorm y hy
    have hconv := hasSum_sum_range_mul_of_summable_norm hfN hgN
    have hfk : (∑' j, ((((k + j).choose k : ℕ)) : ℝ) * y ^ j)
        = (((1 - y) ^ (k + 1))⁻¹) := ih.tsum_eq
    have hgk : (∑' j, y ^ j) = (1 - y)⁻¹ := hg.tsum_eq
    have hprod : (∑' j, ((((k + j).choose k : ℕ)) : ℝ) * y ^ j)
          * (∑' j, y ^ j)
        = (((1 - y) ^ (k + 1 + 1))⁻¹) := by
      rw [hfk, hgk, ← mul_inv, ← pow_succ]
    rw [hprod] at hconv
    apply hconv.congr_fun
    intro n
    have h := chapter9BinomConv y k n
    have e : k + 1 + n = (k + 1) + n := by omega
    rw [e] at h
    exact h.symm

private def chapter9F1 (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2))
    * (-1 : ℝ) ^ p.2
    * (((p.1 + p.2).choose p.1 : ℕ) : ℝ)
    * x ^ (p.1 + 1 + p.2)

private lemma chapter9F1_summable (x : ℝ) (hx : |x| < 1 / 2) :
    Summable (chapter9F1 x) := by
  have h2x : (2 : ℝ) * |x| < 1 := by linarith
  have h2xnn : (0 : ℝ) ≤ 2 * |x| := by positivity
  have hnorm : ‖(2 * |x| : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h2xnn]
    exact h2x
  have hgeo : Summable (fun n : ℕ => (2 * |x|) ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have hgeoNN : (0 : ℕ → ℝ) ≤ (fun n : ℕ => (2 * |x|) ^ n) := by
    intro n
    positivity
  have hprod := hgeo.mul_of_nonneg hgeo hgeoNN hgeoNN
  have hG : Summable (fun p : ℕ × ℕ => |x| * ((2 * |x|) ^ p.1 * (2 * |x|) ^ p.2)) :=
    hprod.mul_left |x|
  apply Summable.of_norm_bounded hG
  intro p
  have hb0 : (0 : ℝ) ≤ 1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hb1 : (1 : ℝ) / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2) ≤ 1 := by
    have h := chapter9LeftWeight_le_one p.1
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h
  have hCnn : (0 : ℝ) ≤ ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ) := by positivity
  have hCle : ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ (p.1 + p.2) := by
    have h := Nat.choose_le_two_pow (p.1 + p.2) p.1
    exact_mod_cast h
  have hbn : ‖(1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2) : ℝ)‖
      = 1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hb0]
  have hneg : ‖((-1 : ℝ) ^ p.2)‖ = 1 := by
    simp only [norm_pow, norm_neg, norm_one, one_pow]
  have hCn : ‖((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)‖
      = ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hCnn]
  have hxn : ‖(x ^ (p.1 + 1 + p.2) : ℝ)‖ = |x| ^ (p.1 + 1 + p.2) := by
    rw [norm_pow, Real.norm_eq_abs]
  have hF : ‖chapter9F1 x p‖
      = (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2))
        * 1 * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
        * |x| ^ (p.1 + 1 + p.2) := by
    unfold chapter9F1
    simp only [norm_mul, hbn, hneg, hCn, hxn]
  rw [hF]
  have hb1' : (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2)) * 1 ≤ 1 * 1 := by
    simpa only [mul_one] using hb1
  have h23 : (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2)) * 1
        * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
      ≤ 1 * 1 * (2 : ℝ) ^ (p.1 + p.2) := by
    apply mul_le_mul hb1' hCle (by positivity) (by positivity)
  have h1 : (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2)) * 1
        * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
        * |x| ^ (p.1 + 1 + p.2)
      ≤ 1 * 1 * (2 : ℝ) ^ (p.1 + p.2) * |x| ^ (p.1 + 1 + p.2) := by
    apply mul_le_mul h23 le_rfl (by positivity) (by positivity)
  have ePowX : |x| ^ (p.1 + 1 + p.2) = |x| ^ (p.1 + p.2) * |x| := by
    have e1 : p.1 + 1 + p.2 = (p.1 + p.2) + 1 := by omega
    rw [e1, pow_add, pow_one]
  have e2 : (2 : ℝ) ^ (p.1 + p.2) * (|x| ^ (p.1 + p.2) * |x|)
      = |x| * ((2 * |x|) ^ p.1 * (2 * |x|) ^ p.2) := by
    have h2 : (2 : ℝ) ^ (p.1 + p.2) = (2 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2 := by
      rw [pow_add]
    have hx12 : |x| ^ (p.1 + p.2) = |x| ^ p.1 * |x| ^ p.2 := by
      rw [pow_add]
    have hm1 : (2 * |x|) ^ p.1 = (2 : ℝ) ^ p.1 * |x| ^ p.1 := by
      rw [mul_pow]
    have hm2 : (2 * |x|) ^ p.2 = (2 : ℝ) ^ p.2 * |x| ^ p.2 := by
      rw [mul_pow]
    rw [h2, hx12, hm1, hm2]
    ring
  calc (1 / (((2 * p.1 + 1 : ℕ) : ℝ) ^ 2)) * 1
          * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
          * |x| ^ (p.1 + 1 + p.2)
        ≤ 1 * 1 * (2 : ℝ) ^ (p.1 + p.2)
          * |x| ^ (p.1 + 1 + p.2) := h1
      _ = 1 * 1 * (2 : ℝ) ^ (p.1 + p.2)
          * (|x| ^ (p.1 + p.2) * |x|) := by
          rw [ePowX]
      _ = (2 : ℝ) ^ (p.1 + p.2) * (|x| ^ (p.1 + p.2) * |x|) := by
          ring
      _ = |x| * ((2 * |x|) ^ p.1 * (2 * |x|) ^ p.2) := e2

private lemma chapter9F1_inner (x : ℝ) (hx1 : |x| < 1) (k : ℕ) :
    (∑' j, chapter9F1 x (k, j)) = chapter9Entry34LeftTerm x k := by
  have hy : ‖-x‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs]
    exact hx1
  have hbin := chapter9BinomHasSum (-x) hy k
  have h1x : (1 : ℝ) - (-x) = 1 + x := by ring
  rw [h1x] at hbin
  have heq : ∀ j : ℕ, chapter9F1 x (k, j)
      = (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) * x ^ (k + 1))
        * (((((k + j).choose k : ℕ)) : ℝ) * (-x) ^ j) := by
    intro j
    unfold chapter9F1
    have e1 : k + 1 + j = (k + 1) + j := by omega
    have e2 : x ^ (k + 1 + j) = x ^ (k + 1) * x ^ j := by
      rw [e1, pow_add]
    have e3 : (-1 : ℝ) ^ j * x ^ j = (-x) ^ j := by
      rw [neg_pow]
      ring
    calc (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2))
            * (-1 : ℝ) ^ j * (((k + j).choose k : ℕ) : ℝ)
            * x ^ (k + 1 + j)
          = (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) * x ^ (k + 1))
            * (((((k + j).choose k : ℕ)) : ℝ) * ((-1 : ℝ) ^ j * x ^ j)) := by
            rw [e2]
            ring
        _ = (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) * x ^ (k + 1))
            * (((((k + j).choose k : ℕ)) : ℝ) * (-x) ^ j) := by
            rw [e3]
  have hHas : HasSum (fun j => chapter9F1 x (k, j))
      ((1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) * x ^ (k + 1))
        * (((1 + x) ^ (k + 1))⁻¹)) := by
    have hmul := hbin.mul_left
      (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) * x ^ (k + 1))
    apply hmul.congr_fun
    intro j
    exact heq j
  rw [hHas.tsum_eq]
  unfold chapter9Entry34LeftTerm
  rw [div_pow, div_eq_mul_inv]
  ring

private lemma chapter9NegOnePowSub (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ k := by
  have h2k : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    simp only [neg_one_sq, one_pow]
  have hn : n + k = (n - k) + 2 * k := by omega
  have hpow : (-1 : ℝ) ^ n * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (n - k) := by
    rw [← pow_add, hn, pow_add, h2k, mul_one]
  exact hpow.symm

private lemma chapter9F1_fiber_term (x : ℝ) (n k : ℕ) (hk : k ≤ n) :
    chapter9F1 x (k, n - k)
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ k * ((n.choose k : ℕ) : ℝ)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) * x ^ (n + 1) := by
  have hpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  have hne : ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt hpos
  have eadd : k + (n - k) = n := Nat.add_sub_cancel' hk
  have eexp : k + 1 + (n - k) = n + 1 := by omega
  have eC : ((k + (n - k)).choose k : ℕ) = n.choose k := by
    rw [eadd]
  have hneg := chapter9NegOnePowSub n k hk
  unfold chapter9F1
  rw [eC, eexp, hneg]
  field_simp

private lemma chapter9F1_fiber (x : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.antidiagonal n, chapter9F1 x (kl.1, kl.2))
      = chapter9Entry34RightTerm x n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k j => chapter9F1 x (k, j)) n]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      chapter9F1 x (k, n - k)
        = x ^ (n + 1) * ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ k
          * ((n.choose k : ℕ) : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [chapter9F1_fiber_term x n k hk]
    ring
  have hsum : (∑ k ∈ Finset.range (n + 1), chapter9F1 x (k, n - k))
      = x ^ (n + 1) * ((-1 : ℝ) ^ n * chapter9AltOddRecipSq n) := by
    unfold chapter9AltOddRecipSq
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hterm k hk]
  rw [hsum, chapter9AltOddRecipSq_eq]
  unfold chapter9Entry34RightTerm chapter9Central
  ring

private lemma chapter9F1_tsum_fiber (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' p : ℕ × ℕ, chapter9F1 x p)
      = ∑' n, ∑ kl ∈ Finset.antidiagonal n, chapter9F1 x (kl.1, kl.2) := by
  have hF := chapter9F1_summable x hx
  conv_rhs => congr
              ext n
              rw [← Finset.sum_finset_coe,
                ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
    (chapter9F1 x)]
  have hFsigma : Summable
      ((chapter9F1 x) ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hF
  exact hFsigma.tsum_sigma' (fun n => (hasSum_fintype _).summable)

private lemma chapter9Dir1 (x : ℝ) (hx : |x| < 1 / 2) :
    (∑' k, chapter9Entry34LeftTerm x k)
      = ∑' k, chapter9Entry34RightTerm x k := by
  have hx1 : |x| < 1 := by linarith
  have hF := chapter9F1_summable x hx
  have hleft : (∑' p : ℕ × ℕ, chapter9F1 x p)
      = ∑' k, chapter9Entry34LeftTerm x k := by
    rw [hF.tsum_prod]
    simp only [chapter9F1_inner x hx1]
  have hright : (∑' p : ℕ × ℕ, chapter9F1 x p)
      = ∑' k, chapter9Entry34RightTerm x k := by
    rw [chapter9F1_tsum_fiber x hx]
    simp only [chapter9F1_fiber x]
  rw [← hleft, hright]

private lemma chapter9SumRangeShift (G : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    (∑ n ∈ Finset.range (m + 1), (if k ≤ n then G (n - k) else 0))
      = ∑ j ∈ Finset.range (m - k + 1), G j := by
  induction m, hk using Nat.le_induction with
  | base =>
    have h1 : ∀ n ∈ Finset.range (k + 1),
        (if k ≤ n then G (n - k) else 0)
          = (if n = k then G 0 else 0) := by
      intro n hn
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hn
      by_cases hkn : k ≤ n
      · have heq : n = k := by omega
        rw [heq]
        simp only [Nat.sub_self]
        have hk_le : k ≤ k := by omega
        simp only [hk_le, ↓reduceIte]
      · simp only [hkn, ↓reduceIte]
        have hne : n ≠ k := by omega
        simp only [hne, ↓reduceIte]
    rw [Finset.sum_congr rfl h1]
    have e : k - k + 1 = 1 := by omega
    rw [e]
    simp only [Finset.sum_range_one]
    rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte]
    · intro n _ hne
      simp only [hne, ↓reduceIte]
    · intro hmem
      simp only [Finset.mem_range, Nat.lt_succ_self] at hmem
      exact False.elim (hmem trivial)
  | succ m hm ih =>
    have hsplit : (∑ n ∈ Finset.range (m + 1 + 1),
          (if k ≤ n then G (n - k) else 0))
        = (∑ n ∈ Finset.range (m + 1),
          (if k ≤ n then G (n - k) else 0))
          + (if k ≤ m + 1 then G (m + 1 - k) else 0) := by
      rw [Finset.sum_range_succ]
    have hk2 : k ≤ m + 1 := by omega
    have hif : (if k ≤ m + 1 then G (m + 1 - k) else 0)
        = G (m + 1 - k) := by
      simp only [hk2, ↓reduceIte]
    have e : m + 1 - k + 1 = (m - k + 1) + 1 := by omega
    have hsplit2 : (∑ j ∈ Finset.range (m + 1 - k + 1), G j)
        = (∑ j ∈ Finset.range (m - k + 1), G j) + G (m - k + 1) := by
      rw [e, Finset.sum_range_succ]
    have e2 : m + 1 - k = m - k + 1 := by omega
    rw [hsplit, hif, hsplit2, ih, e2]

private lemma chapter9BinomInversionInner (b : ℕ → ℝ) (m k : ℕ)
    (hk : k ≤ m) :
    (∑ n ∈ Finset.range (m + 1),
      ((m.choose n : ℕ) : ℝ)
        * ((-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ) * b k))
      = ((m.choose k : ℕ) : ℝ) * b k *
        (∑ j ∈ Finset.range (m - k + 1),
          (-1 : ℝ) ^ j * ((m - k).choose j : ℝ)) := by
  set G : ℕ → ℝ := fun j => ((m.choose (k + j) : ℕ) : ℝ)
    * ((-1 : ℝ) ^ j * (((k + j).choose k : ℕ) : ℝ) * b k) with hGdef
  have hterm : ∀ n ∈ Finset.range (m + 1),
      ((m.choose n : ℕ) : ℝ)
        * ((-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ) * b k)
        = (if k ≤ n then G (n - k) else 0) := by
    intro n _
    by_cases hkn : k ≤ n
    · simp only [hkn, ↓reduceIte]
      have e2 : k + (n - k) = n := Nat.add_sub_cancel' hkn
      have hGreduce : G (n - k)
          = ((m.choose (k + (n - k)) : ℕ) : ℝ)
            * ((-1 : ℝ) ^ (n - k)
              * (((k + (n - k)).choose k : ℕ) : ℝ) * b k) := by
        rw [hGdef]
      rw [hGreduce, e2]
    · simp only [hkn, ↓reduceIte]
      have hkn' : n < k := by omega
      have hC0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hkn'
      simp only [hC0, Nat.cast_zero, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl hterm, chapter9SumRangeShift G m k hk]
  have hGeq : ∀ j ∈ Finset.range (m - k + 1),
      G j = ((m.choose k : ℕ) : ℝ) * b k
        * ((-1 : ℝ) ^ j * ((m - k).choose j : ℝ)) := by
    intro j _
    have hnat := Nat.choose_mul (n := m) (k := k + j) (s := k)
      (Nat.le_add_right k j)
    have hjk : k + j - k = j := by omega
    rw [hjk] at hnat
    have hcast : ((m.choose (k + j) : ℕ) : ℝ)
          * (((k + j).choose k : ℕ) : ℝ)
        = ((m.choose k : ℕ) : ℝ) * (((m - k).choose j : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hGreduce : G j
        = ((m.choose (k + j) : ℕ) : ℝ)
          * ((-1 : ℝ) ^ j * (((k + j).choose k : ℕ) : ℝ) * b k) := by
      rw [hGdef]
    rw [hGreduce]
    linear_combination ((-1 : ℝ) ^ j * b k) * hcast
  rw [Finset.sum_congr rfl hGeq, ← Finset.mul_sum]

private lemma chapter9BinomInversion (b : ℕ → ℝ) (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1),
        ((m.choose n : ℕ) : ℝ)
          * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ) * b k))
      = b m := by
  have hext : ∀ n ∈ Finset.range (m + 1),
      ((m.choose n : ℕ) : ℝ)
          * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ) * b k)
        = ∑ k ∈ Finset.range (m + 1),
          ((m.choose n : ℕ) : ℝ)
            * (((-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ) * b k)) := by
    intro n hn
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hn
    rw [Finset.mul_sum]
    apply Finset.sum_subset
      ((Finset.range_subset_range).mpr (by omega : n + 1 ≤ m + 1))
    intro k _ hknotin
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hknotin
    have hkn : n < k := by omega
    have hC0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hkn
    simp only [hC0, Nat.cast_zero, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl hext]
  rw [Finset.sum_comm]
  have hmem : m ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self m)
  have h0 : ∀ k ∈ Finset.range (m + 1), k ≠ m →
      (∑ n ∈ Finset.range (m + 1),
        ((m.choose n : ℕ) : ℝ)
          * ((-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ) * b k)) = 0 := by
    intro k hk hkm
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [chapter9BinomInversionInner b m k hk]
    have hne : m - k ≠ 0 := by omega
    rw [chapter9AltBinomSum_zero (m - k) hne, mul_zero]
  rw [Finset.sum_eq_single_of_mem m hmem h0]
  have hmle : m ≤ m := by omega
  rw [chapter9BinomInversionInner b m m hmle]
  have e1 : m - m + 1 = 1 := by omega
  rw [e1, Finset.sum_range_one]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.choose_self, one_mul]

private def chapter9CoeffC (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * chapter9AltOddRecipSq n

private lemma chapter9CoeffC_bound (n : ℕ) :
    |chapter9CoeffC n| ≤ (n : ℝ) + 1 := by
  have hCnn := le_of_lt (chapter9Central_pos n)
  have hHnn := chapter9OddHarmonic_nonneg (n + 1)
  have hC1 := chapter9Central_le_one n
  have hH := chapter9OddHarmonic_le (n + 1)
  push_cast at hH
  unfold chapter9CoeffC
  rw [chapter9AltOddRecipSq_eq, abs_mul, abs_mul]
  have hneg : |(-1 : ℝ) ^ n| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [hneg, abs_of_nonneg hCnn, abs_of_nonneg hHnn, one_mul]
  calc chapter9Central n * chapter9OddHarmonic (n + 1)
      ≤ 1 * ((n : ℝ) + 1) :=
        mul_le_mul hC1 hH hHnn zero_le_one
    _ = (n : ℝ) + 1 := one_mul _

private lemma chapter9RightTerm_eq (x : ℝ) (n : ℕ) :
    chapter9Entry34RightTerm x n
      = chapter9CoeffC n * x ^ (n + 1) := by
  unfold chapter9Entry34RightTerm chapter9CoeffC
  rw [chapter9AltOddRecipSq_eq]
  unfold chapter9Central
  ring

private lemma chapter9CoeffC_eq_binom (n : ℕ) :
    chapter9CoeffC n
      = ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ)
          * (1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold chapter9CoeffC chapter9AltOddRecipSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hneg := chapter9NegOnePowSub n k hk
  rw [hneg]
  ring

private lemma chapter9BinomInvApplied (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1),
      ((m.choose n : ℕ) : ℝ) * chapter9CoeffC n)
      = 1 / ((((2 * m + 1 : ℕ)) : ℝ) ^ 2) := by
  have heq : ∀ n ∈ Finset.range (m + 1),
      ((m.choose n : ℕ) : ℝ) * chapter9CoeffC n
        = ((m.choose n : ℕ) : ℝ)
          * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - k) * ((n.choose k : ℕ) : ℝ)
              * (1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) := by
    intro n _
    rw [chapter9CoeffC_eq_binom n]
  rw [Finset.sum_congr rfl heq]
  exact chapter9BinomInversion
    (fun k => 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) m

private def chapter9F2 (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  chapter9CoeffC p.1 * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
    * (x / (1 + x)) ^ (p.1 + 1 + p.2)

private lemma chapter9F2_summable (x : ℝ)
    (ht : |x / (1 + x)| < 1 / 2) :
    Summable (chapter9F2 x) := by
  have h2t : (2 : ℝ) * |x / (1 + x)| < 1 := by linarith
  have h2tnn : (0 : ℝ) ≤ 2 * |x / (1 + x)| := by positivity
  have hnorm : ‖(2 * |x / (1 + x)| : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h2tnn]
    exact h2t
  have hgeo : Summable (fun n : ℕ => (2 * |x / (1 + x)|) ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have harith : Summable
      (fun n : ℕ => ((n : ℝ) + 1) * (2 * |x / (1 + x)|) ^ n) := by
    have h1 : Summable
        (fun n : ℕ => (n : ℝ) ^ 1 * (2 * |x / (1 + x)|) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    have h1' : Summable
        (fun n : ℕ => (n : ℝ) * (2 * |x / (1 + x)|) ^ n) := by
      simpa using h1
    have h3 := h1'.add hgeo
    have heq : (fun n : ℕ => ((n : ℝ) + 1) * (2 * |x / (1 + x)|) ^ n)
        = (fun n : ℕ => (n : ℝ) * (2 * |x / (1 + x)|) ^ n
          + (2 * |x / (1 + x)|) ^ n) := by
      funext n; ring
    rw [heq]; exact h3
  have harithNN : (0 : ℕ → ℝ)
      ≤ (fun n : ℕ => ((n : ℝ) + 1) * (2 * |x / (1 + x)|) ^ n) := by
    intro n
    positivity
  have hgeoNN : (0 : ℕ → ℝ)
      ≤ (fun n : ℕ => (2 * |x / (1 + x)|) ^ n) := by
    intro n
    positivity
  have hprod := harith.mul_of_nonneg hgeo harithNN hgeoNN
  have hG : Summable (fun p : ℕ × ℕ => |x / (1 + x)|
      * ((((p.1 : ℝ) + 1) * (2 * |x / (1 + x)|) ^ p.1)
        * (2 * |x / (1 + x)|) ^ p.2)) :=
    hprod.mul_left |x / (1 + x)|
  apply Summable.of_norm_bounded hG
  intro p
  have hCnn : (0 : ℝ)
      ≤ ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ) := by positivity
  have hCle : ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
      ≤ (2 : ℝ) ^ (p.1 + p.2) := by
    have h := Nat.choose_le_two_pow (p.1 + p.2) p.1
    exact_mod_cast h
  have hc := chapter9CoeffC_bound p.1
  have hcn : ‖chapter9CoeffC p.1‖ = |chapter9CoeffC p.1| :=
    Real.norm_eq_abs _
  have hCn : ‖((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)‖
      = ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hCnn]
  have htn : ‖((x / (1 + x)) ^ (p.1 + 1 + p.2) : ℝ)‖
      = |x / (1 + x)| ^ (p.1 + 1 + p.2) := by
    rw [norm_pow, Real.norm_eq_abs]
  have hF : ‖chapter9F2 x p‖
      = |chapter9CoeffC p.1| * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
        * |x / (1 + x)| ^ (p.1 + 1 + p.2) := by
    unfold chapter9F2
    simp only [norm_mul, hcn, hCn, htn]
  rw [hF]
  have h1 : |chapter9CoeffC p.1|
        * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
        * |x / (1 + x)| ^ (p.1 + 1 + p.2)
      ≤ ((p.1 : ℝ) + 1) * (2 : ℝ) ^ (p.1 + p.2)
        * |x / (1 + x)| ^ (p.1 + 1 + p.2) := by
    apply mul_le_mul _ le_rfl (by positivity) (by positivity)
    exact mul_le_mul hc hCle hCnn (by positivity)
  have ePowT : |x / (1 + x)| ^ (p.1 + 1 + p.2)
      = |x / (1 + x)| ^ (p.1 + p.2) * |x / (1 + x)| := by
    have e1 : p.1 + 1 + p.2 = (p.1 + p.2) + 1 := by omega
    rw [e1, pow_add, pow_one]
  have e2 : ((p.1 : ℝ) + 1) * (2 : ℝ) ^ (p.1 + p.2)
        * (|x / (1 + x)| ^ (p.1 + p.2) * |x / (1 + x)|)
      = |x / (1 + x)|
        * ((((p.1 : ℝ) + 1) * (2 * |x / (1 + x)|) ^ p.1)
          * (2 * |x / (1 + x)|) ^ p.2) := by
    have h2 : (2 : ℝ) ^ (p.1 + p.2)
        = (2 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2 := by rw [pow_add]
    have ht12 : |x / (1 + x)| ^ (p.1 + p.2)
        = |x / (1 + x)| ^ p.1 * |x / (1 + x)| ^ p.2 := by rw [pow_add]
    have hm1 : (2 * |x / (1 + x)|) ^ p.1
        = (2 : ℝ) ^ p.1 * |x / (1 + x)| ^ p.1 := by rw [mul_pow]
    have hm2 : (2 * |x / (1 + x)|) ^ p.2
        = (2 : ℝ) ^ p.2 * |x / (1 + x)| ^ p.2 := by rw [mul_pow]
    rw [h2, ht12, hm1, hm2]
    ring
  calc |chapter9CoeffC p.1| * ((((p.1 + p.2).choose p.1 : ℕ)) : ℝ)
          * |x / (1 + x)| ^ (p.1 + 1 + p.2)
        ≤ ((p.1 : ℝ) + 1) * (2 : ℝ) ^ (p.1 + p.2)
          * |x / (1 + x)| ^ (p.1 + 1 + p.2) := h1
      _ = ((p.1 : ℝ) + 1) * (2 : ℝ) ^ (p.1 + p.2)
          * (|x / (1 + x)| ^ (p.1 + p.2) * |x / (1 + x)|) := by
          rw [ePowT]
      _ = |x / (1 + x)|
          * ((((p.1 : ℝ) + 1) * (2 * |x / (1 + x)|) ^ p.1)
            * (2 * |x / (1 + x)|) ^ p.2) := e2

private lemma chapter9F2_inner (x : ℝ) (ht1 : |x / (1 + x)| < 1)
    (h1x : (0 : ℝ) < 1 + x) (n : ℕ) :
    (∑' i, chapter9F2 x (n, i)) = chapter9Entry34RightTerm x n := by
  have htN : ‖x / (1 + x)‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact ht1
  have hbin := chapter9BinomHasSum (x / (1 + x)) htN n
  have hne : (1 : ℝ) + x ≠ 0 := ne_of_gt h1x
  have h1t : (1 : ℝ) - x / (1 + x) = 1 / (1 + x) := by
    rw [sub_eq_iff_eq_add, ← add_div, div_self hne]
  have heq : ∀ i : ℕ, chapter9F2 x (n, i)
      = (chapter9CoeffC n * (x / (1 + x)) ^ (n + 1))
        * (((((n + i).choose n : ℕ)) : ℝ) * (x / (1 + x)) ^ i) := by
    intro i
    unfold chapter9F2
    have e1 : n + 1 + i = (n + 1) + i := by omega
    have e2 : (x / (1 + x)) ^ (n + 1 + i)
        = (x / (1 + x)) ^ (n + 1) * (x / (1 + x)) ^ i := by
      rw [e1, pow_add]
    rw [e2]
    ring
  have hHas : HasSum (fun i => chapter9F2 x (n, i))
      ((chapter9CoeffC n * (x / (1 + x)) ^ (n + 1))
        * (((1 - x / (1 + x)) ^ (n + 1))⁻¹)) := by
    have hmul := hbin.mul_left
      (chapter9CoeffC n * (x / (1 + x)) ^ (n + 1))
    apply hmul.congr_fun
    intro i
    exact heq i
  rw [hHas.tsum_eq, chapter9RightTerm_eq, h1t,
    div_pow, div_pow, one_pow, inv_div, div_one]
  have hpow : ((1 : ℝ) + x) ^ (n + 1) ≠ 0 := pow_ne_zero _ hne
  rw [mul_assoc, div_mul_cancel₀ _ hpow]

private lemma chapter9F2_fiber (x : ℝ) (m : ℕ) :
    (∑ kl ∈ Finset.antidiagonal m, chapter9F2 x (kl.1, kl.2))
      = chapter9Entry34LeftTerm x m := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k j => chapter9F2 x (k, j)) m]
  have hterm : ∀ k ∈ Finset.range (m + 1),
      chapter9F2 x (k, m - k)
        = (x / (1 + x)) ^ (m + 1)
          * (((m.choose k : ℕ) : ℝ) * chapter9CoeffC k) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have eadd : k + (m - k) = m := Nat.add_sub_cancel' hk
    have eexp : k + 1 + (m - k) = m + 1 := by omega
    have eC : (k + (m - k)).choose k = m.choose k := by rw [eadd]
    unfold chapter9F2
    rw [eC, eexp]
    ring
  have hsum : (∑ k ∈ Finset.range (m + 1), chapter9F2 x (k, m - k))
      = (x / (1 + x)) ^ (m + 1)
        * (∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℕ) : ℝ) * chapter9CoeffC k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hterm k hk]
  rw [hsum, chapter9BinomInvApplied m]
  unfold chapter9Entry34LeftTerm
  ring

private lemma chapter9F2_tsum_fiber (x : ℝ)
    (ht : |x / (1 + x)| < 1 / 2) :
    (∑' p : ℕ × ℕ, chapter9F2 x p)
      = ∑' m, ∑ kl ∈ Finset.antidiagonal m, chapter9F2 x (kl.1, kl.2) := by
  have hF := chapter9F2_summable x ht
  conv_rhs => congr
              ext m
              rw [← Finset.sum_finset_coe,
                ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
    (chapter9F2 x)]
  have hFsigma : Summable
      ((chapter9F2 x) ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hF
  exact hFsigma.tsum_sigma' (fun m => (hasSum_fintype _).summable)

private lemma chapter9Dir2 (x : ℝ) (h1x : (0 : ℝ) < 1 + x)
    (ht : |x / (1 + x)| < 1 / 2) :
    (∑' k, chapter9Entry34LeftTerm x k)
      = ∑' k, chapter9Entry34RightTerm x k := by
  have ht1 : |x / (1 + x)| < 1 := by linarith
  have hF := chapter9F2_summable x ht
  have hleft : (∑' p : ℕ × ℕ, chapter9F2 x p)
      = ∑' m, chapter9Entry34LeftTerm x m := by
    rw [chapter9F2_tsum_fiber x ht]
    simp only [chapter9F2_fiber x]
  have hright : (∑' p : ℕ × ℕ, chapter9F2 x p)
      = ∑' n, chapter9Entry34RightTerm x n := by
    rw [hF.tsum_prod]
    simp only [chapter9F2_inner x ht1 h1x]
  rw [← hleft, hright]

/-- **Ramanujan's series identity with odd harmonic numbers (Entry 34).** For a natural number
$m$ let $O_m = \sum_{j=0}^{m-1} 1/(2j+1)$. Let $x$ be real with $-1/2 < x < 1$. Then
$1 + x > 0$, $|x| < 1$ and $|x/(1+x)| < 1$, the series
$\sum_{k \ge 0} \frac{1}{(2k+1)^2} \left(\frac{x}{1+x}\right)^{k+1}$ and
$\sum_{k \ge 0} \frac{(-1)^k\, 2^{2k} (k!)^2}{(2k+1)!} O_{k+1} x^{k+1}$ converge absolutely, and
their sums are equal.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry34_zeta3doublesum
    (x : ℝ) (hxLower : -(1 / 2 : ℝ) < x) (hxUpper : x < 1) :
    0 < 1 + x ∧
      |x| < 1 ∧
      |x / (1 + x)| < 1 ∧
      Summable (chapter9Entry34LeftTerm x) ∧
      Summable (chapter9Entry34RightTerm x) ∧
      (∑' k : ℕ, chapter9Entry34LeftTerm x k) =
        ∑' k : ℕ, chapter9Entry34RightTerm x k := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hx_abs : |x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have ht_abs : |x / (1 + x)| < 1 := by
    rw [abs_div, abs_of_pos h1x, div_lt_one h1x, abs_lt]
    constructor <;> linarith
  refine ⟨h1x, hx_abs, ht_abs, summable_chapter9Entry34LeftTerm x ht_abs,
    summable_chapter9Entry34RightTerm x hx_abs, ?_⟩
  by_cases hx2 : |x| < 1 / 2
  · exact chapter9Dir1 x hx2
  · have hxge : (1 / 2 : ℝ) ≤ |x| := le_of_not_gt hx2
    have hxnn : (1 / 2 : ℝ) ≤ x := by
      by_cases hx0 : 0 ≤ x
      · rw [abs_of_nonneg hx0] at hxge
        exact hxge
      · push Not at hx0
        rw [abs_of_neg hx0] at hxge
        linarith
    have hpos : (0 : ℝ) < x / (1 + x) := div_pos (by linarith) h1x
    have ht2 : |x / (1 + x)| < 1 / 2 := by
      rw [abs_of_pos hpos, div_lt_iff₀ h1x]
      linarith
    exact chapter9Dir2 x h1x ht2

end
end Entry34Zeta3doublesum
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
