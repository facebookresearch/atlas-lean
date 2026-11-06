/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry20Piseries1
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry21Piseries2

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal
import MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

This module proves `ramanujan_part1_ch9_entry22_chudnovsky`, Entry 22 on the
corrected range `0 ≤ x ≤ π / 4`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry22Chudnovsky

open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries

open scoped Nat Real BigOperators Interval
open Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Chi3Term (j : ℕ) : ℝ :=
  1 / (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def chapter9Chi3AtOne : ℝ :=
  ∑' j : ℕ, chapter9Chi3Term j

def chapter9Entry22CentralTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

def chapter9Entry23FactorialTerm (u : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
    (((2 * k + 1).factorial : ℝ) * (((2 * k + 2 : ℕ) : ℝ) ^ 2))

def chapter9Entry22LeftTerm (x : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23FactorialTerm x k +
    chapter9Entry23FactorialTerm (Real.pi / 2 - x) k

/-- **Odd reciprocal cubes in Entries 21 and 22.** The sequence $j \mapsto 1/(2j+1)^3$
($j = 0, 1, 2, \dots$) used in the statement of Entry 22 of Chapter 9 of Ramanujan's notebooks
is, by definition, the same sequence as the one used in Entry 21. -/
theorem chapter9Chi3Term_eq_entry21 :
    chapter9Chi3Term = Entry21Piseries2.chapter9Chi3Term := rfl

/-- **The sum of the odd reciprocal cubes in Entries 21 and 22.** The constant
$\sum_{j \ge 0} 1/(2j+1)^3$ used in the statement of Entry 22 of Chapter 9 of Ramanujan's
notebooks is, by definition, the same constant as the one used in Entry 21. -/
theorem chapter9Chi3AtOne_eq_entry21 :
    chapter9Chi3AtOne = Entry21Piseries2.chapter9Chi3AtOne := rfl

/-- **The factorial sine series term in Entries 20 and 22.** For real $u$ and $k \ge 0$, the
term $2^{2k} (k!)^2 \sin^{2k+2} u / \bigl((2k+1)! \, (2k+2)^2\bigr)$ used in the statement of
Entry 22 of Chapter 9 of Ramanujan's notebooks is, by definition, the same as the one used in
Entry 20. -/
theorem chapter9Entry23FactorialTerm_eq_entry20 :
    chapter9Entry23FactorialTerm = Entry20Piseries1.chapter9Entry23FactorialTerm := rfl

private lemma base2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hp
  simpa using h

private lemma base3 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) 1).mpr hp
  simpa using h

private lemma factbound (k : ℕ) : 4 ^ k * (k.factorial ^ 2) ≤ (2 * k + 1).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have key : 4 * (k + 1) ^ 2 ≤ (2 * (k + 1) + 1) * (2 * (k + 1)) := by
      have h : (2 * (k + 1) + 1) * (2 * (k + 1))
          = 4 * (k + 1) ^ 2 + 2 * (k + 1) := by ring
      rw [h]
      exact Nat.le_add_right _ _
    calc 4 ^ (k + 1) * ((k + 1).factorial ^ 2)
        = (4 * (k + 1) ^ 2) * (4 ^ k * (k.factorial ^ 2)) := by
          rw [pow_succ, Nat.factorial_succ k]
          ring
      _ ≤ ((2 * (k + 1) + 1) * (2 * (k + 1))) * (2 * k + 1).factorial :=
          mul_le_mul key ih (Nat.zero_le _) (Nat.zero_le _)
      _ = (2 * (k + 1) + 1).factorial := by
          have f1 := Nat.factorial_succ (2 * (k + 1))
          have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
          have f2 : (2 * (k + 1)).factorial
              = (2 * (k + 1)) * (2 * k + 1).factorial := by
            have f := Nat.factorial_succ (2 * k + 1)
            rwa [← e] at f
          rw [f1, f2, mul_assoc]

private lemma hFratio (k : ℕ) :
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2)
      / (((2 * k + 1).factorial : ℝ)) ≤ 1 := by
  have hF : (0 : ℝ) < ((((2 * k + 1).factorial) : ℕ) : ℝ) := by
    have h : 0 < (2 * k + 1).factorial := Nat.factorial_pos _
    exact_mod_cast h
  rw [div_le_one hF]
  have hfb := factbound k
  have h' : ((4 ^ k * (k.factorial ^ 2) : ℕ) : ℝ)
      ≤ (((((2 * k + 1).factorial) : ℕ)) : ℝ) :=
    Nat.cast_le.mpr hfb
  have h4 : (4 : ℝ) ^ k * (((k.factorial : ℕ)) : ℝ) ^ 2
      = (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) := by
    congr 1
    have h42 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h42, ← pow_mul]
  rw [← h4]
  push_cast at h'
  exact h'

private lemma chi3_summable : Summable chapter9Chi3Term := by
  rw [chapter9Chi3Term_eq_entry21]
  exact (Entry21Piseries2.ramanujan_part1_ch9_entry21_piseries2 0 (by
    rw [abs_zero]
    positivity)).1

private lemma central_summable (x : ℝ) :
    Summable (chapter9Entry22CentralTerm x) := by
  have hcos : ‖Real.cos x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one x
  exact (summable_arcsinIntegralSeries_term (Real.cos x) hcos).congr (fun k => by
    rw [arcsinIntegralSeries_term_eq]
    rfl)

private lemma factorial_summable (u : ℝ) (hu : |u| ≤ Real.pi / 2) :
    Summable (chapter9Entry23FactorialTerm u) := by
  rw [chapter9Entry23FactorialTerm_eq_entry20]
  exact (Entry20Piseries1.ramanujan_part1_ch9_entry20_piseries1 u hu).2.2.1

private def aCoeff (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
    (((2 * k + 1).factorial : ℝ))

private lemma aCoeff_nonneg (k : ℕ) : 0 ≤ aCoeff k := by
  unfold aCoeff
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply mul_nonneg _ (pow_nonneg (Nat.cast_nonneg _) _)
  exact pow_nonneg (by norm_num) _

private lemma aCoeff_le_one (k : ℕ) : aCoeff k ≤ 1 := by
  unfold aCoeff
  exact hFratio k

private lemma e22_recip_term_eq (x : ℝ) (m : ℕ) :
    (2 * x) ^ (2 * (m + 1)) / ((((m + 1 : ℕ)) : ℝ) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ))
      = 2 * aCoeff m * x ^ (2 * (m + 1)) := by
  have hle : m + 1 ≤ 2 * (m + 1) := by omega
  have hch := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : 2 * (m + 1) - (m + 1) = m + 1 := by omega
  rw [hsub] at hch
  have hchr : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)
        * (((m + 1).factorial : ℕ) : ℝ) * (((m + 1).factorial : ℕ) : ℝ)
        = ((((2 * (m + 1)).factorial : ℕ)) : ℝ) := by exact_mod_cast hch
  have hCf : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) ≠ 0 := by
    have h : 0 < Nat.choose (2 * (m + 1)) (m + 1) := Nat.choose_pos hle
    exact_mod_cast ne_of_gt h
  have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  have hFn : ((((m + 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hCeq : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)
      = ((((2 * (m + 1)).factorial : ℕ)) : ℝ)
        / (((((m + 1).factorial : ℕ)) : ℝ) * ((((m + 1).factorial : ℕ)) : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hFn hFn)]
    linear_combination hchr
  have hF1 : ((((m + 1).factorial : ℕ)) : ℝ) = ((m : ℝ) + 1) * ((m.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hF2 : ((((2 * (m + 1)).factorial : ℕ)) : ℝ)
      = (2 * ((m : ℝ) + 1)) * ((((2 * m + 1).factorial : ℕ)) : ℝ) := by
    have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    conv_lhs => rw [e1]
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hF1ne : ((m.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2ne : ((((2 * m + 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hMne : (m : ℝ) + 1 ≠ 0 := by positivity
  have hcastm : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hpow : (2 * x) ^ (2 * (m + 1)) = (2 : ℝ) ^ (2 * (m + 1)) * x ^ (2 * (m + 1)) := by
    rw [mul_pow]
  have h2pow : (2 : ℝ) ^ (2 * (m + 1)) = 4 * (2 : ℝ) ^ (2 * m) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
    ring
  unfold aCoeff
  rw [hpow, h2pow, hCeq, hF1, hF2, hcastm]
  field_simp
  ring

private lemma e22a_hasSum_ne {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasSum (fun m : ℕ => aCoeff m * x ^ (2 * m + 1))
      (Real.arcsin x / Real.sqrt (1 - x ^ 2)) := by
  have H := MetaMathlibExt.arcsin_central_binomial_reciprocal_series x hx
  have H2 : HasSum (fun m : ℕ => 2 * aCoeff m * x ^ (2 * (m + 1)))
      ((2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x) :=
    H.congr_fun (fun m => (e22_recip_term_eq x m).symm)
  have h2x : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx0
  have hx2 : (0 : ℝ) < 1 - x ^ 2 := by
    have hsq1 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
    linarith
  have hsq : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hx2
  have H3 := H2.div_const (2 * x)
  have hterm : (fun m : ℕ => (2 * aCoeff m * x ^ (2 * (m + 1))) / (2 * x))
      = (fun m : ℕ => aCoeff m * x ^ (2 * m + 1)) := by
    funext m
    have hpow : x ^ (2 * (m + 1)) = x ^ (2 * m + 1) * x := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ]
    rw [hpow]
    field_simp
  have hval : (((2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x) / (2 * x))
      = Real.arcsin x / Real.sqrt (1 - x ^ 2) := by
    field_simp
  rw [hterm, hval] at H3
  exact H3

private lemma e22a_hasSum_zero :
    HasSum (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 1))
      (Real.arcsin 0 / Real.sqrt (1 - (0 : ℝ) ^ 2)) := by
  have hfun : (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 1)) = fun _ => 0 := by
    funext m
    have hz : (0 : ℝ) ^ (2 * m + 1) = 0 := zero_pow (by omega)
    rw [hz, mul_zero]
  rw [hfun]
  have hval : Real.arcsin 0 / Real.sqrt (1 - (0 : ℝ) ^ 2) = 0 := by
    rw [Real.arcsin_zero, zero_div]
  rw [hval]
  exact hasSum_zero

private lemma e22a_hasSum {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ => aCoeff m * x ^ (2 * m + 1))
      (Real.arcsin x / Real.sqrt (1 - x ^ 2)) := by
  by_cases hx0 : x = 0
  · subst hx0
    exact e22a_hasSum_zero
  · exact e22a_hasSum_ne hx hx0

private def e22A (t : ℝ) : ℝ :=
  ∑' m : ℕ, aCoeff m * t ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)

private lemma e22A_term_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => aCoeff m * s ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ))
      (aCoeff m * t ^ (2 * m + 1)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * m + 2))
      (((2 * m + 2 : ℕ) : ℝ) * t ^ (2 * m + 1)) t := by
    have h := hasDerivAt_pow (2 * m + 2) t
    have heq : (2 * m + 2) - 1 = 2 * m + 1 := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (aCoeff m)
  have hdiv := hmul.div_const ((2 * m + 2 : ℕ) : ℝ)
  have hsimp : aCoeff m * (((2 * m + 2 : ℕ) : ℝ) * t ^ (2 * m + 1)) /
        ((2 * m + 2 : ℕ) : ℝ) = aCoeff m * t ^ (2 * m + 1) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma e22A_majorant (r : ℝ) (_hr0 : 0 < r) (hr1 : r < 1) (m : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ioo (-r) r) :
    ‖aCoeff m * y ^ (2 * m + 1)‖ ≤ (r ^ 2) ^ m := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    rw [Set.mem_Ioo] at hy
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hc : ‖aCoeff m‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff_nonneg m)]
    exact aCoeff_le_one m
  have hpow_le : ‖y‖ ^ (2 * m + 1) ≤ r ^ (2 * m + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have h1 : ‖aCoeff m‖ * ‖y‖ ^ (2 * m + 1) ≤ 1 * r ^ (2 * m + 1) :=
    mul_le_mul hc hpow_le (by positivity) (by norm_num)
  have hrr : r ^ (2 * m + 1) ≤ (r ^ 2) ^ m := by
    have hle : r ≤ 1 := le_of_lt hr1
    have hnn : (0 : ℝ) ≤ r ^ (2 * m) := by positivity
    have heq : r ^ (2 * m + 1) = r ^ (2 * m) * r := by rw [pow_succ]
    have heq2 : (r ^ 2) ^ m = r ^ (2 * m) * 1 := by
      rw [← pow_mul, mul_one]
    rw [heq, heq2]
    exact mul_le_mul_of_nonneg_left hle hnn
  calc ‖aCoeff m * y ^ (2 * m + 1)‖
        = ‖aCoeff m‖ * ‖y‖ ^ (2 * m + 1) := by rw [norm_mul, norm_pow]
      _ ≤ 1 * r ^ (2 * m + 1) := h1
      _ = r ^ (2 * m + 1) := by ring
      _ ≤ (r ^ 2) ^ m := hrr

private lemma e22A_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt e22A (∑' m : ℕ, aCoeff m * y ^ (2 * m + 1)) y := by
  have hu : Summable (fun m : ℕ => (r ^ 2) ^ m) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ m : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun s : ℝ => aCoeff m * s ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ))
        (aCoeff m * z ^ (2 * m + 1)) z :=
    fun m z _ => e22A_term_hasDerivAt m z
  have hbound : ∀ m : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖aCoeff m * z ^ (2 * m + 1)‖ ≤ (r ^ 2) ^ m :=
    fun m z hz => e22A_majorant r hr0 hr1 m z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun m : ℕ =>
      aCoeff m * (0 : ℝ) ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)) := by
    have hzero : (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ))
        = fun _ => 0 := by
      funext m
      have hz : (0 : ℝ) ^ (2 * m + 2) = 0 := zero_pow (by omega)
      rw [hz, mul_zero, zero_div]
    rw [hzero]
    exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma e22A_zero : e22A 0 = 0 := by
  unfold e22A
  have hzero : (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ))
      = fun _ => 0 := by
    funext m
    have hz : (0 : ℝ) ^ (2 * m + 2) = 0 := zero_pow (by omega)
    rw [hz, mul_zero, zero_div]
  rw [hzero, tsum_zero]

private lemma e22A_hasDerivAt_arcsin {y : ℝ} (hy : ‖y‖ < 1) :
    HasDerivAt e22A (Real.arcsin y / Real.sqrt (1 - y ^ 2)) y := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have habs : |y| < (‖y‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    linarith [hy]
  rw [abs_lt] at habs
  have hymem : y ∈ Set.Ioo (-((‖y‖ + 1) / 2)) ((‖y‖ + 1) / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hder := e22A_hasDerivAt_of_mem hr0 hr1 hymem
  have habs1 : |y| < 1 := by
    rw [← Real.norm_eq_abs]
    exact hy
  have hsum := e22a_hasSum habs1
  rw [hsum.tsum_eq] at hder
  exact hder

private lemma e22_arcsin_sq_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => Real.arcsin t ^ 2 / 2)
      (Real.arcsin x / Real.sqrt (1 - x ^ 2)) x := by
  rw [Set.mem_Ioo] at hx
  have h1 : x ≠ -1 := by linarith [hx.1]
  have h2 : x ≠ 1 := by linarith [hx.2]
  have h_arc : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin h1 h2
  have h_sq : HasDerivAt (fun t : ℝ => Real.arcsin t ^ 2)
      (2 * Real.arcsin x * (1 / Real.sqrt (1 - x ^ 2))) x := by
    have h2 := h_arc.mul h_arc
    have heq : (Real.arcsin * Real.arcsin)
        = (fun t : ℝ => Real.arcsin t ^ 2) := by
      funext t
      rw [Pi.mul_apply, pow_two]
    rw [heq] at h2
    refine h2.congr_deriv ?_
    ring
  have h_div := h_sq.div_const (2 : ℝ)
  have hsimp : (2 * Real.arcsin x * (1 / Real.sqrt (1 - x ^ 2))) / 2
      = Real.arcsin x / Real.sqrt (1 - x ^ 2) := by
    ring
  rwa [hsimp] at h_div

private lemma e22A_eq_arcsin_sq :
    Set.EqOn e22A (fun t : ℝ => Real.arcsin t ^ 2 / 2) (Set.Ioo (-1 : ℝ) 1) := by
  have hopen : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-1 : ℝ) 1) := isPreconnected_Ioo
  have hAdiff : DifferentiableOn ℝ e22A (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hnorm : ‖x‖ < 1 := by
      rw [Real.norm_eq_abs, abs_lt]
      exact hx
    have h := e22A_hasDerivAt_arcsin hnorm
    exact (h.differentiableAt).differentiableWithinAt
  have hsq_diff : DifferentiableOn ℝ (fun t : ℝ => Real.arcsin t ^ 2 / 2)
      (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact ((e22_arcsin_sq_hasDerivAt hx).differentiableAt).differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv e22A)
      (deriv (fun t : ℝ => Real.arcsin t ^ 2 / 2)) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hnorm : ‖x‖ < 1 := by
      rw [Real.norm_eq_abs, abs_lt]
      exact hx
    have hA := e22A_hasDerivAt_arcsin hnorm
    have hS := e22_arcsin_sq_hasDerivAt hx
    rw [hA.deriv, hS.deriv]
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h0eq : e22A 0 = Real.arcsin 0 ^ 2 / 2 := by
    rw [e22A_zero, Real.arcsin_zero]
    norm_num
  exact IsOpen.eqOn_of_deriv_eq hopen hpre hAdiff hsq_diff hderiv_eq h0mem h0eq

private def e22S (t : ℝ) : ℝ :=
  ∑' m : ℕ, aCoeff m * t ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2

private lemma e22_factorial_eq_aCoeff (u : ℝ) (m : ℕ) :
    chapter9Entry23FactorialTerm u m
      = aCoeff m * Real.sin u ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2 := by
  unfold chapter9Entry23FactorialTerm aCoeff
  ring

private lemma e22S_sin_eq_tsum (u : ℝ) :
    e22S (Real.sin u) = ∑' m : ℕ, chapter9Entry23FactorialTerm u m := by
  unfold e22S
  congr 1
  funext m
  rw [e22_factorial_eq_aCoeff]

private lemma e22S_term_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => aCoeff m * s ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2)
      (aCoeff m * t ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * m + 2))
      (((2 * m + 2 : ℕ) : ℝ) * t ^ (2 * m + 1)) t := by
    have h := hasDerivAt_pow (2 * m + 2) t
    have heq : (2 * m + 2) - 1 = 2 * m + 1 := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (aCoeff m)
  have hdiv := hmul.div_const (((2 * m + 2 : ℕ) : ℝ) ^ 2)
  have hsimp : aCoeff m * (((2 * m + 2 : ℕ) : ℝ) * t ^ (2 * m + 1)) /
        ((2 * m + 2 : ℕ) : ℝ) ^ 2
      = aCoeff m * t ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma e22_one_div_two_le (m : ℕ) : (1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((2 * m + 2 : ℕ) : ℝ) := by
    have hle : 1 ≤ 2 * m + 2 := by omega
    exact_mod_cast hle
  calc (1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ) ≤ 1 / 1 := by
        apply one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by simp

private lemma e22S_majorant (r : ℝ) (_hr0 : 0 < r) (hr1 : r < 1) (m : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ioo (-r) r) :
    ‖aCoeff m * y ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ)‖ ≤ (r ^ 2) ^ m := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    rw [Set.mem_Ioo] at hy
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hc : ‖aCoeff m‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff_nonneg m)]
    exact aCoeff_le_one m
  have hd : ‖(1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact e22_one_div_two_le m
  have hpow_le : ‖y‖ ^ (2 * m + 1) ≤ r ^ (2 * m + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have h1 : ‖aCoeff m‖ * ‖y‖ ^ (2 * m + 1) ≤ 1 * r ^ (2 * m + 1) :=
    mul_le_mul hc hpow_le (by positivity) (by norm_num)
  have h2 : (‖aCoeff m‖ * ‖y‖ ^ (2 * m + 1)) * ‖(1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ)‖ ≤
      (1 * r ^ (2 * m + 1)) * 1 :=
    mul_le_mul h1 hd (by positivity) (by positivity)
  have heq : ‖aCoeff m * y ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ)‖
      = (‖aCoeff m‖ * ‖y‖ ^ (2 * m + 1)) * ‖(1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ)‖ := by
    rw [div_eq_mul_one_div]
    simp [norm_mul, norm_pow, mul_assoc]
  have hrr : r ^ (2 * m + 1) ≤ (r ^ 2) ^ m := by
    have hle : r ≤ 1 := le_of_lt hr1
    have hnn : (0 : ℝ) ≤ r ^ (2 * m) := by positivity
    have heq1 : r ^ (2 * m + 1) = r ^ (2 * m) * r := by rw [pow_succ]
    have heq2 : (r ^ 2) ^ m = r ^ (2 * m) * 1 := by
      rw [← pow_mul, mul_one]
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left hle hnn
  rw [heq]
  calc (‖aCoeff m‖ * ‖y‖ ^ (2 * m + 1)) * ‖1 / ((2 * m + 2 : ℕ) : ℝ)‖
        ≤ (1 * r ^ (2 * m + 1)) * 1 := h2
      _ = r ^ (2 * m + 1) := by ring
      _ ≤ (r ^ 2) ^ m := hrr

private lemma e22S_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt e22S (∑' m : ℕ, aCoeff m * y ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ)) y := by
  have hu : Summable (fun m : ℕ => (r ^ 2) ^ m) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ m : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun s : ℝ => aCoeff m * s ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2)
        (aCoeff m * z ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ)) z :=
    fun m z _ => e22S_term_hasDerivAt m z
  have hbound : ∀ m : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖aCoeff m * z ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ)‖ ≤ (r ^ 2) ^ m :=
    fun m z hz => e22S_majorant r hr0 hr1 m z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 2) /
      ((2 * m + 2 : ℕ) : ℝ) ^ 2) := by
    have hzero : (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 2) /
        ((2 * m + 2 : ℕ) : ℝ) ^ 2) = fun _ => 0 := by
      funext m
      have hz : (0 : ℝ) ^ (2 * m + 2) = 0 := zero_pow (by omega)
      rw [hz, mul_zero, zero_div]
    rw [hzero]
    exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma e22A_summable_at {y : ℝ} (hy : ‖y‖ < 1) :
    Summable (fun m : ℕ => aCoeff m * y ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)) := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have hr : ‖y‖ < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hu : Summable (fun m : ℕ => ((((‖y‖ + 1) / 2) ^ 2) ^ m)) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hu
  have hyr : ‖y‖ < (‖y‖ + 1) / 2 := hr
  have hc : ‖aCoeff m‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff_nonneg m)]
    exact aCoeff_le_one m
  have hd : ‖(1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact e22_one_div_two_le m
  have hpow : ‖y‖ ^ (2 * m + 2) ≤ ((‖y‖ + 1) / 2) ^ (2 * m + 2) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have hpow2 : ((‖y‖ + 1) / 2) ^ (2 * m + 2) ≤ ((‖y‖ + 1) / 2) ^ (2 * m) := by
    have hr1' : ((‖y‖ + 1) / 2) ^ 2 ≤ 1 := by nlinarith [hr0, hr1]
    have hnn : (0 : ℝ) ≤ ((‖y‖ + 1) / 2) ^ (2 * m) := by positivity
    have heq1 : ((‖y‖ + 1) / 2) ^ (2 * m + 2)
        = ((‖y‖ + 1) / 2) ^ (2 * m) * (((‖y‖ + 1) / 2) ^ 2) := by
      rw [pow_add]
    rw [heq1]
    calc ((‖y‖ + 1) / 2) ^ (2 * m) * (((‖y‖ + 1) / 2) ^ 2)
          ≤ ((‖y‖ + 1) / 2) ^ (2 * m) * 1 :=
            mul_le_mul_of_nonneg_left hr1' hnn
        _ = ((‖y‖ + 1) / 2) ^ (2 * m) := by ring
  calc ‖aCoeff m * y ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)‖
        = (‖aCoeff m‖ * ‖y‖ ^ (2 * m + 2)) * ‖(1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ)‖ := by
          rw [div_eq_mul_one_div]
          simp [norm_mul, norm_pow, mul_assoc]
      _ ≤ (1 * ((‖y‖ + 1) / 2) ^ (2 * m + 2)) * 1 := by
          have h1 : ‖aCoeff m‖ * ‖y‖ ^ (2 * m + 2) ≤
              1 * ((‖y‖ + 1) / 2) ^ (2 * m + 2) :=
            mul_le_mul hc hpow (by positivity) (by norm_num)
          exact mul_le_mul h1 hd (by positivity) (by positivity)
      _ ≤ ((((‖y‖ + 1) / 2) ^ 2) ^ m) := by
          calc (1 * ((‖y‖ + 1) / 2) ^ (2 * m + 2)) * 1
                = ((‖y‖ + 1) / 2) ^ (2 * m + 2) := by ring
            _ ≤ ((‖y‖ + 1) / 2) ^ (2 * m) := hpow2
            _ = ((((‖y‖ + 1) / 2) ^ 2) ^ m) := by
              exact pow_mul _ 2 m

private lemma e22S_hasDerivAt_arcsin_sq {y : ℝ} (hy : ‖y‖ < 1) (hy0 : y ≠ 0) :
    HasDerivAt e22S (Real.arcsin y ^ 2 / (2 * y)) y := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have habs : |y| < (‖y‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  rw [abs_lt] at habs
  have hymem : y ∈ Set.Ioo (-((‖y‖ + 1) / 2)) ((‖y‖ + 1) / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hS := e22S_hasDerivAt_of_mem hr0 hr1 hymem
  have hAsum := e22A_summable_at hy
  have hterm : (fun m : ℕ => aCoeff m * y ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ))
      = (fun m : ℕ => (aCoeff m * y ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)) * y⁻¹) := by
    funext m
    have hne : ((2 * m + 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hpow : y ^ (2 * m + 2) = y ^ (2 * m + 1) * y := by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, pow_succ]
    rw [hpow]
    field_simp
  have hsum_eq : (∑' m : ℕ, aCoeff m * y ^ (2 * m + 1) / ((2 * m + 2 : ℕ) : ℝ))
      = (∑' m : ℕ, aCoeff m * y ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ)) / y := by
    rw [hterm, hAsum.tsum_mul_right, div_eq_mul_inv]
  have hAval : (∑' m : ℕ, aCoeff m * y ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ))
      = Real.arcsin y ^ 2 / 2 := by
    have heq : e22A y = Real.arcsin y ^ 2 / 2 :=
      e22A_eq_arcsin_sq (by
        rw [Set.mem_Ioo, ← abs_lt, ← Real.norm_eq_abs]
        exact hy)
    unfold e22A at heq
    exact heq
  rw [hsum_eq, hAval] at hS
  have hsimp : (Real.arcsin y ^ 2 / 2) / y = Real.arcsin y ^ 2 / (2 * y) := by
    ring
  rw [hsimp] at hS
  exact hS

private lemma e22S_zero : e22S 0 = 0 := by
  unfold e22S
  have hzero : (fun m : ℕ => aCoeff m * (0 : ℝ) ^ (2 * m + 2) /
      ((2 * m + 2 : ℕ) : ℝ) ^ 2) = fun _ => 0 := by
    funext m
    have hz : (0 : ℝ) ^ (2 * m + 2) = 0 := zero_pow (by omega)
    rw [hz, mul_zero, zero_div]
  rw [hzero, tsum_zero]

private lemma e22S_bound (t : ℝ) (ht : ‖t‖ ≤ 1) (m : ℕ) :
    ‖aCoeff m * t ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2‖ ≤
      (1 : ℝ) / (((m : ℝ) + 1) ^ 2) := by
  have hc : ‖aCoeff m‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff_nonneg m)]
    exact aCoeff_le_one m
  have hpow : ‖t‖ ^ (2 * m + 2) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht
  have h1 : ‖aCoeff m‖ * ‖t‖ ^ (2 * m + 2) ≤ 1 := by
    calc ‖aCoeff m‖ * ‖t‖ ^ (2 * m + 2) ≤ 1 * 1 :=
          mul_le_mul hc hpow (by positivity) (by norm_num)
      _ = 1 := by ring
  have hcast : ((2 * m + 2 : ℕ) : ℝ) = 2 * ((m : ℝ) + 1) := by push_cast; ring
  have hsq : ((2 * m + 2 : ℕ) : ℝ) ^ 2 = 4 * (((m : ℝ) + 1) ^ 2) := by
    rw [hcast]
    ring
  have hpos : (0 : ℝ) < (((m : ℝ) + 1) ^ 2) := by positivity
  have hDnn : (0 : ℝ) ≤ ((2 * m + 2 : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD : ‖((2 * m + 2 : ℕ) : ℝ) ^ 2‖ = ((2 * m + 2 : ℕ) : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hDnn]
  have heq : ‖aCoeff m * t ^ (2 * m + 2) / ((2 * m + 2 : ℕ) : ℝ) ^ 2‖
      = (‖aCoeff m‖ * ‖t‖ ^ (2 * m + 2)) / ((2 * m + 2 : ℕ) : ℝ) ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, hD]
  rw [heq, hsq]
  calc (‖aCoeff m‖ * ‖t‖ ^ (2 * m + 2)) / (4 * (((m : ℝ) + 1) ^ 2))
        ≤ 1 / (4 * (((m : ℝ) + 1) ^ 2)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact h1
      _ ≤ 1 / (((m : ℝ) + 1) ^ 2) := by
          apply one_div_le_one_div_of_le hpos
          nlinarith [hpos]

private lemma e22S_continuousOn : ContinuousOn e22S (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum (fun m => ?_) base2 (fun m x hx => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * m + 2)).continuousOn
  · have ht : ‖x‖ ≤ 1 := by
      rw [Set.mem_Icc] at hx
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    exact e22S_bound x ht m

private lemma e22F_cos_eq_tsum (x : ℝ) :
    arcsinIntegralSeries (Real.cos x) = ∑' k : ℕ, chapter9Entry22CentralTerm x k := by
  unfold arcsinIntegralSeries chapter9Entry22CentralTerm
  congr 1
  funext k
  unfold centralBinomialCoeff
  ring

private lemma e22_sin_cos_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ ∈ Set.Ioo 0 1 ∧ Real.cos θ ∈ Set.Ioo 0 1 := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hθ
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith)
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin_ne : Real.sin θ ≠ 1 := by
    intro h
    have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at hsq
    nlinarith [hsq, hcos_pos, sq_nonneg (Real.cos θ)]
  have hcos_ne : Real.cos θ ≠ 1 := by
    intro h
    have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at hsq
    nlinarith [hsq, hsin_pos, sq_nonneg (Real.sin θ)]
  refine ⟨⟨hsin_pos, lt_of_le_of_ne (Real.sin_le_one θ) hsin_ne⟩,
    ⟨hcos_pos, lt_of_le_of_ne (Real.cos_le_one θ) hcos_ne⟩⟩

private lemma e22_norm_ne_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖Real.sin θ‖ < 1 ∧ ‖Real.cos θ‖ < 1 ∧ Real.sin θ ≠ 0 ∧ Real.cos θ ≠ 0 := by
  have hmem := e22_sin_cos_mem_Ioo hθ
  simp only [Set.mem_Ioo] at hmem
  have hsin_norm : ‖Real.sin θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hmem.1.1, hmem.1.2]
  have hcos_norm : ‖Real.cos θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hmem.2.1, hmem.2.2]
  exact ⟨hsin_norm, hcos_norm, ne_of_gt hmem.1.1, ne_of_gt hmem.2.1⟩

private lemma e22_mem_pi_div_two_of_pi_div_four {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    x ∈ Set.Ioo 0 (Real.pi / 2) ∧ 2 * x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hx ⊢
  constructor
  · constructor <;> linarith [hx.1, hx.2]
  · constructor <;> linarith [hx.1, hx.2]

private lemma e22_arcsin_sin_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.arcsin (Real.sin θ) = θ := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hθ
  exact Real.arcsin_sin (by linarith) (by linarith)

private lemma e22_arcsin_cos_of_mem {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    Real.arcsin (Real.cos x) = Real.pi / 2 - x := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hx
  have hmem : Real.pi / 2 - x ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [hx.1, hx.2]
  have hsin : Real.sin (Real.pi / 2 - x) = Real.cos x := Real.sin_pi_div_two_sub x
  have harcsin := e22_arcsin_sin_of_mem hmem
  rw [hsin] at harcsin
  exact harcsin

private def e22H (x : ℝ) : ℝ :=
  (e22S (Real.sin x) + e22S (Real.cos x))
    - (-(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x)
      + Real.pi / 2 * arcsinIntegralSeries (Real.cos x)
      + (1 / 4 : ℝ) * e22S (Real.sin (2 * x))
      - (1 / 2 : ℝ) * chapter9Chi3AtOne)

private lemma e22_two_mul_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
  simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)

private lemma e22_sin_two_mul_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * x) * 2) x :=
  (Real.hasDerivAt_sin (2 * x)).comp x (e22_two_mul_hasDerivAt x)

private lemma e22_Ssin_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt (fun x : ℝ => e22S (Real.sin x))
      ((Real.arcsin (Real.sin x) ^ 2 / (2 * Real.sin x)) * Real.cos x) x := by
  have hmem := e22_mem_pi_div_two_of_pi_div_four hx
  have hnorm := e22_norm_ne_of_mem_Ioo hmem.1
  have houter := e22S_hasDerivAt_arcsin_sq hnorm.1 hnorm.2.2.1
  exact houter.comp x (Real.hasDerivAt_sin x)

private lemma e22_Scos_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt (fun x : ℝ => e22S (Real.cos x))
      ((Real.arcsin (Real.cos x) ^ 2 / (2 * Real.cos x)) * (-Real.sin x)) x := by
  have hmem := e22_mem_pi_div_two_of_pi_div_four hx
  have hnorm := e22_norm_ne_of_mem_Ioo hmem.1
  have houter := e22S_hasDerivAt_arcsin_sq hnorm.2.1 hnorm.2.2.2
  exact houter.comp x (Real.hasDerivAt_cos x)

private lemma e22_Fcos_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt (fun x : ℝ => arcsinIntegralSeries (Real.cos x))
      ((Real.arcsin (Real.cos x) / Real.cos x) * (-Real.sin x)) x := by
  have hmem := e22_mem_pi_div_two_of_pi_div_four hx
  have hnorm := e22_norm_ne_of_mem_Ioo hmem.1
  have houter := hasDerivAt_arcsinIntegralSeries hnorm.2.1 hnorm.2.2.2
  exact houter.comp x (Real.hasDerivAt_cos x)

private lemma e22_Ssin2_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt (fun x : ℝ => e22S (Real.sin (2 * x)))
      ((Real.arcsin (Real.sin (2 * x)) ^ 2 / (2 * Real.sin (2 * x))) *
        (Real.cos (2 * x) * 2)) x := by
  have hmem := e22_mem_pi_div_two_of_pi_div_four hx
  have hnorm := e22_norm_ne_of_mem_Ioo hmem.2
  have houter := e22S_hasDerivAt_arcsin_sq hnorm.1 hnorm.2.2.1
  exact houter.comp x (e22_sin_two_mul_hasDerivAt x)

private lemma e22_log_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt (fun x : ℝ => Real.log (2 * Real.cos x))
      ((2 * Real.cos x)⁻¹ * (2 * (-Real.sin x))) x := by
  have hmem := e22_mem_pi_div_two_of_pi_div_four hx
  have hcos_pos : 0 < Real.cos x := (e22_sin_cos_mem_Ioo hmem.1).2.1
  have hne : 2 * Real.cos x ≠ 0 := ne_of_gt (by linarith)
  have houter := Real.hasDerivAt_log hne
  have hinner : HasDerivAt (fun x : ℝ => 2 * Real.cos x) (2 * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul 2
  exact houter.comp x hinner

private lemma e22H_hasDerivAt_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt e22H 0 x := by
  have hmem := e22_mem_pi_div_two_of_pi_div_four hx
  have hnorm := e22_norm_ne_of_mem_Ioo hmem.1
  have hnorm2 := e22_norm_ne_of_mem_Ioo hmem.2
  have hsin_ne : Real.sin x ≠ 0 := hnorm.2.2.1
  have hcos_ne : Real.cos x ≠ 0 := hnorm.2.2.2
  have hsin2_ne : Real.sin (2 * x) ≠ 0 := hnorm2.2.2.1
  have harcsin_sin := e22_arcsin_sin_of_mem hmem.1
  have harcsin_cos := e22_arcsin_cos_of_mem hx
  have harcsin_sin2 : Real.arcsin (Real.sin (2 * x)) = 2 * x :=
    e22_arcsin_sin_of_mem hmem.2
  have hSsin := e22_Ssin_hasDerivAt hx
  have hScos := e22_Scos_hasDerivAt hx
  have hFcos := e22_Fcos_hasDerivAt hx
  have hSsin2 := e22_Ssin2_hasDerivAt hx
  have hlog := e22_log_hasDerivAt hx
  have hlogpart : HasDerivAt
      (fun x : ℝ => -(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x))
      (-(Real.pi ^ 2 / 8) * ((2 * Real.cos x)⁻¹ * (2 * (-Real.sin x)))) x :=
    hlog.const_mul (-(Real.pi ^ 2 / 8))
  have hFpart : HasDerivAt (fun x : ℝ => Real.pi / 2 * arcsinIntegralSeries (Real.cos x))
      ((Real.pi / 2) * ((Real.arcsin (Real.cos x) / Real.cos x) * (-Real.sin x))) x :=
    hFcos.const_mul (Real.pi / 2)
  have hS2part : HasDerivAt (fun x : ℝ => (1 / 4 : ℝ) * e22S (Real.sin (2 * x)))
      ((1 / 4 : ℝ) *
        ((Real.arcsin (Real.sin (2 * x)) ^ 2 / (2 * Real.sin (2 * x))) *
          (Real.cos (2 * x) * 2))) x :=
    hSsin2.const_mul (1 / 4 : ℝ)
  have hchi : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ) * chapter9Chi3AtOne) 0 x :=
    hasDerivAt_const x _
  have hLHS := hSsin.add hScos
  have hRHS12 := hlogpart.add hFpart
  have hRHS123 := hRHS12.add hS2part
  have hRHS := hRHS123.sub hchi
  have hsin2x : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x :=
    Real.sin_two_mul x
  have hcos2x : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 :=
    Real.cos_two_mul' x
  unfold e22H
  refine (hLHS.sub hRHS).congr_deriv ?_
  rw [harcsin_sin, harcsin_cos, harcsin_sin2, hsin2x, hcos2x]
  field_simp
  ring

private lemma e22_cos_pos_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    0 < Real.cos x := by
  have hpi := Real.pi_pos
  rw [Set.mem_Icc] at hx
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma e22_sin_cos_mem_Icc (t : ℝ) : Real.sin t ∈ Set.Icc (-1 : ℝ) 1 ∧
    Real.cos t ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ⟨⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩,
    ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩⟩

private lemma e22H_continuousOn : ContinuousOn e22H (Set.Icc 0 (Real.pi / 4)) := by
  have hF := continuousOn_arcsinIntegralSeries
  have hS := e22S_continuousOn
  have hcos_on : ContinuousOn Real.cos (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_cos.continuousOn
  have hsin_on : ContinuousOn Real.sin (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_sin.continuousOn
  have hsin2_on : ContinuousOn (fun x : ℝ => Real.sin (2 * x))
      (Set.Icc 0 (Real.pi / 4)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hSsin : ContinuousOn (fun x : ℝ => e22S (Real.sin x))
      (Set.Icc 0 (Real.pi / 4)) :=
    hS.comp hsin_on (fun x _ => (e22_sin_cos_mem_Icc x).1)
  have hScos : ContinuousOn (fun x : ℝ => e22S (Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) :=
    hS.comp hcos_on (fun x _ => (e22_sin_cos_mem_Icc x).2)
  have hFcos : ContinuousOn (fun x : ℝ => arcsinIntegralSeries (Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) :=
    hF.comp hcos_on (fun x _ => (e22_sin_cos_mem_Icc x).2)
  have hSsin2 : ContinuousOn (fun x : ℝ => e22S (Real.sin (2 * x)))
      (Set.Icc 0 (Real.pi / 4)) :=
    hS.comp hsin2_on (fun x _ => (e22_sin_cos_mem_Icc (2 * x)).1)
  have h2cos_on : ContinuousOn (fun x : ℝ => 2 * Real.cos x)
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul hcos_on
  have hlog_on : ContinuousOn (fun x : ℝ => Real.log (2 * Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) := by
    have hlog := Real.continuousOn_log
    refine hlog.comp h2cos_on (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hpos := e22_cos_pos_of_mem_Icc hx
    linarith
  have hLHS : ContinuousOn (fun x : ℝ => e22S (Real.sin x) + e22S (Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) :=
    hSsin.add hScos
  have hlogpart : ContinuousOn
      (fun x : ℝ => -(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul hlog_on
  have hFpart : ContinuousOn (fun x : ℝ => Real.pi / 2 * arcsinIntegralSeries (Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul hFcos
  have hS2part : ContinuousOn (fun x : ℝ => (1 / 4 : ℝ) * e22S (Real.sin (2 * x)))
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul hSsin2
  have hRHS12 := hlogpart.add hFpart
  have hRHS123 := hRHS12.add hS2part
  have hRHS : ContinuousOn
      (fun x : ℝ => -(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x)
        + Real.pi / 2 * arcsinIntegralSeries (Real.cos x)
        + (1 / 4 : ℝ) * e22S (Real.sin (2 * x))
        - (1 / 2 : ℝ) * chapter9Chi3AtOne)
      (Set.Icc 0 (Real.pi / 4)) :=
    hRHS123.sub continuousOn_const
  have h := hLHS.sub hRHS
  unfold e22H
  exact h

private lemma e22_sinc_pos_of_mem_Icc {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 < Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    rw [Real.sinc_zero]
    norm_num
  · rw [Real.sinc_of_ne_zero h0]
    have hpi := Real.pi_pos
    rw [Set.mem_Icc] at hθ
    have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    exact div_pos hsin hpos

private lemma e22_sin_eq_mul_sinc (θ : ℝ) :
    Real.sin θ = θ * Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    simp only [Real.sin_zero, Real.sinc_zero, zero_mul]
  · rw [Real.sinc_of_ne_zero h0]
    field_simp

private lemma e22_ulogsin_continuousOn :
    ContinuousOn (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (Set.Icc 0 (Real.pi / 2)) := by
  have hB : ContinuousOn (fun θ : ℝ => θ * Real.log θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_mul_log.continuousOn
  have hsinc_on : ContinuousOn Real.sinc (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_sinc.continuousOn
  have hlog_sinc_on : ContinuousOn (fun θ : ℝ => Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuousOn_log.comp hsinc_on (fun θ hθ => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (e22_sinc_pos_of_mem_Icc hθ))
  have hC : ContinuousOn (fun θ : ℝ => θ * Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_id.mul hlog_sinc_on
  have hBC : ContinuousOn
      (fun θ : ℝ => θ * Real.log θ + θ * Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    hB.add hC
  have hEq : Set.EqOn (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (fun θ : ℝ => θ * Real.log θ + θ * Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) := by
    intro θ hθ
    by_cases h0 : θ = 0
    · subst h0
      simp only [Real.sin_zero, Real.log_zero, Real.sinc_zero, Real.log_one,
        zero_mul, add_zero]
    · have hsinc_ne : Real.sinc θ ≠ 0 :=
        ne_of_gt (e22_sinc_pos_of_mem_Icc hθ)
      have hsin_eq := e22_sin_eq_mul_sinc θ
      have hlog : Real.log (Real.sin θ)
          = Real.log θ + Real.log (Real.sinc θ) := by
        rw [hsin_eq, Real.log_mul h0 hsinc_ne]
      change θ * Real.log (Real.sin θ) = θ * Real.log θ + θ * Real.log (Real.sinc θ)
      rw [hlog, mul_add]
  exact hBC.congr hEq

private def e22Q (u : ℝ) : ℝ := u * Real.cos u / (2 * Real.sinc u)

private lemma e22Q_continuousOn :
    ContinuousOn e22Q (Set.Icc 0 (Real.pi / 2)) := by
  have hnum : ContinuousOn (fun u : ℝ => u * Real.cos u)
      (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_id.mul Real.continuous_cos.continuousOn
  have hden : ContinuousOn (fun u : ℝ => 2 * Real.sinc u)
      (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_const.mul Real.continuous_sinc.continuousOn
  have hne : ∀ u ∈ Set.Icc 0 (Real.pi / 2), (2 : ℝ) * Real.sinc u ≠ 0 := by
    intro u hu
    have hsinc : Real.sinc u ≠ 0 := ne_of_gt (e22_sinc_pos_of_mem_Icc hu)
    exact mul_ne_zero (by norm_num) hsinc
  have h := hnum.div hden hne
  unfold e22Q
  exact h

private lemma e22P_hasDerivAt {u : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun u : ℝ => e22S (Real.sin u)) (e22Q u) u := by
  have hnorm := e22_norm_ne_of_mem_Ioo hu
  have houter := e22S_hasDerivAt_arcsin_sq hnorm.1 hnorm.2.2.1
  have hcomp : HasDerivAt (fun u : ℝ => e22S (Real.sin u))
      ((Real.arcsin (Real.sin u) ^ 2 / (2 * Real.sin u)) * Real.cos u) u :=
    houter.comp u (Real.hasDerivAt_sin u)
  have harcsin := e22_arcsin_sin_of_mem hu
  rw [harcsin] at hcomp
  have hne : u ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hu).1
  have hsin_ne : Real.sin u ≠ 0 := hnorm.2.2.1
  have hDeq : (u ^ 2 / (2 * Real.sin u)) * Real.cos u = e22Q u := by
    unfold e22Q
    rw [Real.sinc_of_ne_zero hne]
    field_simp
  rw [hDeq] at hcomp
  exact hcomp

private lemma e22P_continuousOn :
    ContinuousOn (fun u : ℝ => e22S (Real.sin u)) (Set.Icc 0 (Real.pi / 2)) := by
  exact e22S_continuousOn.comp Real.continuous_sin.continuousOn
    (fun u _ => (e22_sin_cos_mem_Icc u).1)

private lemma e22S_one_eq_integral_Q :
    e22S 1 = ∫ u in (0 : ℝ)..(Real.pi / 2), e22Q u := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hcont := e22P_continuousOn
  have hderiv : ∀ u ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun u : ℝ => e22S (Real.sin u)) (e22Q u) u :=
    fun u hu => e22P_hasDerivAt hu
  have hint : IntervalIntegrable e22Q MeasureTheory.volume 0 (Real.pi / 2) :=
    e22Q_continuousOn.intervalIntegrable_of_Icc hle
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
    hderiv hint
  have hsin_pi2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have hP_pi2 : e22S (Real.sin (Real.pi / 2)) = e22S 1 := by rw [hsin_pi2]
  have hP0 : e22S (Real.sin 0) = 0 := by rw [Real.sin_zero, e22S_zero]
  rw [hP_pi2, hP0, sub_zero] at hFTC
  exact hFTC.symm

private def e22K (u : ℝ) : ℝ := u ^ 2 / 2 * Real.log (Real.sin u)

private lemma e22K_continuousOn :
    ContinuousOn e22K (Set.Icc 0 (Real.pi / 2)) := by
  have hA := e22_ulogsin_continuousOn
  have hHalf : ContinuousOn (fun u : ℝ => u / 2) (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_id.div_const 2
  have hEq : e22K = (fun u : ℝ => (u / 2) * (u * Real.log (Real.sin u))) := by
    funext u
    unfold e22K
    ring
  rw [hEq]
  exact hHalf.mul hA

private lemma e22K_hasDerivAt {u : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt e22K
      ((u * Real.log (Real.sin u)) + e22Q u) u := by
  have hne : u ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hu).1
  have hnorm := e22_norm_ne_of_mem_Ioo hu
  have hsin_ne : Real.sin u ≠ 0 := hnorm.2.2.1
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
    have h := (hasDerivAt_pow 2 u).div_const (2 : ℝ)
    have hsimp : ((2 : ℕ) : ℝ) * u ^ (2 - 1) / 2 = u := by
      norm_num
    rwa [hsimp] at h
  have hlogsin : HasDerivAt (fun u : ℝ => Real.log (Real.sin u))
      ((Real.sin u)⁻¹ * Real.cos u) u :=
    (Real.hasDerivAt_log hsin_ne).comp u (Real.hasDerivAt_sin u)
  have hK0 := hsq.mul hlogsin
  have heqF : ((fun u : ℝ => u ^ 2 / 2) * (fun u : ℝ => Real.log (Real.sin u)))
      = e22K := by
    funext v
    simp [Pi.mul_apply, e22K]
  rw [heqF] at hK0
  have hDeq : (u * Real.log (Real.sin u) + u ^ 2 / 2 * ((Real.sin u)⁻¹ * Real.cos u))
      = ((u * Real.log (Real.sin u)) + e22Q u) := by
    have hQ : u ^ 2 / 2 * ((Real.sin u)⁻¹ * Real.cos u) = e22Q u := by
      unfold e22Q
      rw [Real.sinc_of_ne_zero hne]
      field_simp
    rw [hQ]
  have hK1 : HasDerivAt e22K
      (u * Real.log (Real.sin u) + u ^ 2 / 2 * ((Real.sin u)⁻¹ * Real.cos u)) u :=
    hK0
  rwa [hDeq] at hK1

private lemma e22S_one_eq_neg_integral_ulogsin :
    e22S 1 = -∫ u in (0 : ℝ)..(Real.pi / 2), u * Real.log (Real.sin u) := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hAint : IntervalIntegrable (fun u : ℝ => u * Real.log (Real.sin u))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    e22_ulogsin_continuousOn.intervalIntegrable_of_Icc hle
  have hQint : IntervalIntegrable e22Q MeasureTheory.volume 0 (Real.pi / 2) :=
    e22Q_continuousOn.intervalIntegrable_of_Icc hle
  have hAQint : IntervalIntegrable
      (fun u : ℝ => (u * Real.log (Real.sin u)) + e22Q u)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    hAint.add hQint
  have hcont := e22K_continuousOn
  have hderiv : ∀ u ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt e22K ((u * Real.log (Real.sin u)) + e22Q u) u :=
    fun u hu => e22K_hasDerivAt hu
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
    hderiv hAQint
  have hKpi2 : e22K (Real.pi / 2) = 0 := by
    unfold e22K
    rw [Real.sin_pi_div_two, Real.log_one, mul_zero]
  have hK0 : e22K 0 = 0 := by
    unfold e22K
    simp
  rw [hKpi2, hK0, sub_zero] at hFTC
  have hadd := intervalIntegral.integral_add hAint hQint
  have hS1 := e22S_one_eq_integral_Q
  have hJ : (∫ u in (0 : ℝ)..(Real.pi / 2),
      ((u * Real.log (Real.sin u)) + e22Q u))
      = (∫ u in (0 : ℝ)..(Real.pi / 2), u * Real.log (Real.sin u)) + e22S 1 := by
    rw [hadd, hS1]
  rw [hJ] at hFTC
  linarith [hFTC]

private lemma e22_exp_I_mul_ofReal (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) =
      ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  have h : (Complex.I * (t : ℂ)) = ((t : ℂ)) * Complex.I := mul_comm _ _
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma e22_norm_exp_I_mul (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

private lemma e22_cpow (r x : ℝ) (n : ℕ) :
    (((r : ℝ) : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))) ^ (n + 1)
      = (((r ^ (n + 1) * Real.cos ((((n + 1 : ℕ)) : ℝ) * (2 * x)) : ℝ)) : ℂ)
        + (((r ^ (n + 1) * Real.sin ((((n + 1 : ℕ)) : ℝ) * (2 * x)) : ℝ)) : ℂ) *
          Complex.I := by
  rw [mul_pow]
  have hE : (Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))) ^ (n + 1)
      = (((Real.cos ((((n + 1 : ℕ)) : ℝ) * (2 * x)) : ℝ)) : ℂ)
        + (((Real.sin ((((n + 1 : ℕ)) : ℝ) * (2 * x)) : ℝ)) : ℂ) * Complex.I := by
    rw [← Complex.exp_nat_mul]
    have harg : ((n + 1 : ℕ) : ℂ) * (Complex.I * (((2 * x : ℝ)) : ℂ))
        = Complex.I * ((((((n + 1 : ℕ)) : ℝ) * (2 * x) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [harg, e22_exp_I_mul_ofReal]
  rw [hE]
  push_cast
  ring

private lemma e22_cre (r x : ℝ) (n : ℕ) :
    ((((r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))) ^ (n + 1) /
      ((n : ℂ) + 1))).re
      = r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1) := by
  have hD : ((n : ℂ) + 1) = Complex.ofReal ((n : ℝ) + 1) := by
    push_cast
    ring
  have hcos : Real.cos ((((n + 1 : ℕ)) : ℝ) * (2 * x))
      = Real.cos (2 * ((n : ℝ) + 1) * x) := by
    congr 1
    push_cast
    ring
  rw [e22_cpow, hcos, hD, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, sub_zero]
  rw [div_eq_mul_inv]

private lemma e22_poisson {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖
      = -∑' n : ℕ, r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x)
        / ((n : ℝ) + 1) := by
  set z : ℂ := (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ)) with hz
  have hnorm : ‖z‖ < 1 := by
    rw [hz, norm_mul, e22_norm_exp_I_mul, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have H := Complex.hasSum_taylorSeries_neg_log' hnorm
  have hsum : Summable (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) :=
    H.summable
  have hre_tsum : (∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1)).re
      = ∑' n : ℕ, (z ^ (n + 1) / ((n : ℂ) + 1)).re :=
    Complex.re_tsum hsum
  have htsum_eq := H.tsum_eq
  have hlog_re : (-Complex.log (1 - z)).re
      = -Real.log ‖(1 : ℂ) - z‖ := by
    rw [Complex.neg_re, Complex.log_re]
  rw [← htsum_eq] at hlog_re
  rw [hre_tsum] at hlog_re
  have hterm : (fun n : ℕ => (z ^ (n + 1) / ((n : ℂ) + 1)).re)
      = (fun n : ℕ => r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x)
        / ((n : ℝ) + 1)) := by
    funext n
    rw [hz]
    exact e22_cre r x n
  rw [hterm] at hlog_re
  have hnorm_eq : ‖(1 : ℂ) - z‖
      = ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ := by
    rw [hz]
  rw [hnorm_eq] at hlog_re
  linarith [hlog_re]

private lemma e22_integral_u_mul_cos (k : ℕ) :
    ∫ u in (0 : ℝ)..((k : ℝ) * Real.pi), u * Real.cos u
      = ((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi)
        + Real.cos ((k : ℝ) * Real.pi) - 1 := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u => u * Real.sin u + Real.cos u)
      (u * Real.cos u) u := by
    intro u
    have h := ((hasDerivAt_id' u).mul (Real.hasDerivAt_sin u)).add
      (Real.hasDerivAt_cos u)
    have heq : (1 * Real.sin u + u * Real.cos u) + -Real.sin u
        = u * Real.cos u := by ring
    rwa [heq] at h
  have hdiff : ∀ u ∈ [[(0 : ℝ), (k : ℝ) * Real.pi]],
      DifferentiableAt ℝ (fun u => u * Real.sin u + Real.cos u) u :=
    fun u _ => (hF u).differentiableAt
  have hdeq : deriv (fun u => u * Real.sin u + Real.cos u)
      = (fun u => u * Real.cos u) :=
    funext fun u => (hF u).deriv
  have hint : IntervalIntegrable (deriv (fun u => u * Real.sin u + Real.cos u))
      MeasureTheory.volume (0 : ℝ) ((k : ℝ) * Real.pi) := by
    rw [hdeq]
    exact (continuous_id.mul Real.continuous_cos).intervalIntegrable _ _
  rw [← hdeq, intervalIntegral.integral_deriv_eq_sub hdiff hint]
  simp [Real.cos_zero]

private lemma e22_integral_x_mul_cos_two_mul (n : ℕ) :
    ∫ x in (0 : ℝ)..(Real.pi / 2), x * Real.cos (2 * ((n : ℝ) + 1) * x)
      = ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 2)) := by
  have hk : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hc : (2 : ℝ) * ((n : ℝ) + 1) ≠ 0 := mul_ne_zero (by norm_num) hk
  have hfun : (fun x : ℝ => x * Real.cos (2 * ((n : ℝ) + 1) * x))
      = (fun x => ((2 : ℝ) * ((n : ℝ) + 1))⁻¹ *
        ((fun u => u * Real.cos u) (((2 : ℝ) * ((n : ℝ) + 1)) * x))) := by
    funext x
    field_simp
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun u => u * Real.cos u) hc,
    smul_eq_mul, mul_zero]
  have harg : (2 : ℝ) * ((n : ℝ) + 1) * (Real.pi / 2)
      = ((n + 1 : ℕ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [harg, e22_integral_u_mul_cos]
  have hsin : Real.sin ((((n + 1 : ℕ)) : ℝ) * Real.pi) = 0 :=
    Real.sin_nat_mul_pi (n + 1)
  have hcos : Real.cos ((((n + 1 : ℕ)) : ℝ) * Real.pi) = (-1 : ℝ) ^ (n + 1) :=
    Real.cos_nat_mul_pi (n + 1)
  have hcast : ((((n + 1 : ℕ)) : ℝ) : ℝ) = ((n : ℝ) + 1) := by
    push_cast
    ring
  rw [hsin, hcos, hcast]
  field_simp
  ring

private lemma e22_poisson_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ x in (0 : ℝ)..(Real.pi / 2),
        x * Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖
      = ∑' n : ℕ, r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) / (4 * (((n : ℝ) + 1) ^ 3)) := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  set f : ℕ → ℝ → ℝ := fun n x =>
    x * (r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)) with hf
  have hM_sum : Summable (fun n : ℕ => (Real.pi / 2) * r ^ (n + 1)) := by
    have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) := by
      have h : Summable (fun n : ℕ => r ^ n) :=
        summable_geometric_of_norm_lt_one (by
          rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
      have hshift := (summable_nat_add_iff 1).mpr h
      simpa [pow_add] using hshift
    exact hgeo.mul_left (Real.pi / 2)
  have hbound : ∀ n : ℕ, ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      ‖f n x‖ ≤ (Real.pi / 2) * r ^ (n + 1) := by
    intro n x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hle] at hx
      exact hx
    rw [Set.mem_Icc] at hxmem
    have habs : |x| ≤ Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [hxmem.1, hxmem.2]
    have hcos : |Real.cos (2 * ((n : ℝ) + 1) * x)| ≤ 1 := Real.abs_cos_le_one _
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have hle1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      calc (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 1 :=
            one_div_le_one_div_of_le (by norm_num) hle1
        _ = 1 := by simp
    have hnn : (0 : ℝ) ≤ r ^ (n + 1) := pow_nonneg hr0 _
    calc ‖f n x‖ = |x| * (r ^ (n + 1) * |Real.cos (2 * ((n : ℝ) + 1) * x)| / ((n : ℝ) + 1)) := by
          unfold f
          rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_of_nonneg hnn,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
        _ ≤ (Real.pi / 2) * (r ^ (n + 1) * 1 / ((n : ℝ) + 1)) := by
          apply mul_le_mul habs _ (by positivity) (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hcos hnn
        _ ≤ (Real.pi / 2) * r ^ (n + 1) := by
          have : r ^ (n + 1) * 1 / ((n : ℝ) + 1) ≤ r ^ (n + 1) := by
            have h1' : r ^ (n + 1) / ((n : ℝ) + 1) ≤ r ^ (n + 1) := by
              calc r ^ (n + 1) / ((n : ℝ) + 1)
                    = r ^ (n + 1) * (1 / ((n : ℝ) + 1)) := by ring
                  _ ≤ r ^ (n + 1) * 1 := by
                      apply mul_le_mul_of_nonneg_left h1 hnn
                  _ = r ^ (n + 1) := by ring
            simpa using h1'
          exact mul_le_mul_of_nonneg_left this (by linarith)
  have hunif : TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.range N, f n x)
      (fun x : ℝ => ∑' n : ℕ, f n x) Filter.atTop (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    tendstoUniformlyOn_tsum_nat hM_sum hbound
  have hfncont : ∀ n : ℕ, ContinuousOn (fun x : ℝ => f n x)
      (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    intro n
    unfold f
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn
  have hcontN : ∀ᶠ N : ℕ in Filter.atTop,
      ContinuousOn (fun x : ℝ => ∑ n ∈ Finset.range N, f n x)
        (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    apply Filter.Eventually.of_forall
    intro N
    induction N with
    | zero =>
      simpa using continuousOn_const
    | succ N ih =>
      have hEq : (fun x : ℝ => ∑ n ∈ Finset.range (N + 1), f n x)
          = (fun x => (∑ n ∈ Finset.range N, f n x) + f N x) := by
        funext x
        rw [Finset.sum_range_succ]
      rw [hEq]
      exact ih.add (hfncont N)
  have hlim : Filter.Tendsto
      (fun N : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2), ∑ n ∈ Finset.range N, f n x)
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..(Real.pi / 2), ∑' n : ℕ, f n x)) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn hcontN hunif
  have hfin : ∀ N : ℕ, ∫ x in (0 : ℝ)..(Real.pi / 2),
        ∑ n ∈ Finset.range N, f n x
      = ∑ n ∈ Finset.range N, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x := by
    intro N
    rw [intervalIntegral.integral_finsetSum]
    intro n _
    have hc := hfncont n
    rw [Set.uIcc_of_le hle] at hc
    exact hc.intervalIntegrable_of_Icc hle
  have hterm_int : ∀ n : ℕ, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x
      = r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 3)) := by
    intro n
    have hfac : (fun x : ℝ => f n x)
        = (fun x => (r ^ (n + 1) / ((n : ℝ) + 1)) * (x * Real.cos (2 * ((n : ℝ) + 1) * x))) := by
      funext x
      unfold f
      ring
    rw [hfac, intervalIntegral.integral_const_mul, e22_integral_x_mul_cos_two_mul]
    field_simp
  have hInt_sum : Summable (fun n : ℕ =>
      ∫ x in (0 : ℝ)..(Real.pi / 2), f n x) := by
    have hEq : (fun n : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2), f n x)
        = (fun n : ℕ => r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1)
          / (4 * (((n : ℝ) + 1) ^ 3))) :=
      funext hterm_int
    rw [hEq]
    have hle : ∀ n : ℕ,
        ‖r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 3))‖
          ≤ 1 / (((n : ℝ) + 1) ^ 3) := by
      intro n
      have hr1' : r ^ (n + 1) ≤ 1 := by
        calc r ^ (n + 1) ≤ 1 ^ (n + 1) :=
              pow_le_pow_left₀ hr0 (le_of_lt hr1) _
          _ = 1 := one_pow _
      have hnn : (0 : ℝ) ≤ r ^ (n + 1) := pow_nonneg hr0 _
      have habs : |(-1 : ℝ) ^ (n + 1) - 1| ≤ 2 := by
        have h1 : |(-1 : ℝ) ^ (n + 1)| ≤ 1 := by
          rw [abs_pow]
          simp
        calc |(-1 : ℝ) ^ (n + 1) - 1| ≤ |(-1 : ℝ) ^ (n + 1)| + |1| := abs_sub _ _
          _ ≤ 1 + 1 := by
              have : |(1 : ℝ)| = 1 := abs_one
              rw [this]
              linarith [h1]
          _ = 2 := by norm_num
      have hpos : (0 : ℝ) < (((n : ℝ) + 1) ^ 3) := by positivity
      calc ‖r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 3))‖
            = (r ^ (n + 1) * |(-1 : ℝ) ^ (n + 1) - 1|) / (4 * (((n : ℝ) + 1) ^ 3)) := by
              rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hnn,
                abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (((n : ℝ) + 1) ^ 3))]
          _ ≤ (1 * 2) / (4 * (((n : ℝ) + 1) ^ 3)) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul hr1' habs (by positivity) (by norm_num)
          _ ≤ 1 / (((n : ℝ) + 1) ^ 3) := by
              have hX : (0 : ℝ) < (((n : ℝ) + 1) ^ 3) := by positivity
              have hXne : (((n : ℝ) + 1) ^ 3) ≠ 0 := ne_of_gt hX
              have h4Xne : (4 : ℝ) * (((n : ℝ) + 1) ^ 3) ≠ 0 :=
                mul_ne_zero (by norm_num) hXne
              field_simp
              nlinarith [hX]
    exact Summable.of_norm_bounded base3 hle
  have htsum_lim : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x)
      Filter.atTop (nhds (∑' n : ℕ, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x)) :=
    hInt_sum.hasSum.tendsto_sum_nat
  have huniq : (∫ x in (0 : ℝ)..(Real.pi / 2), ∑' n : ℕ, f n x)
      = ∑' n : ℕ, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x := by
    have h1 : Filter.Tendsto
        (fun N : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2), ∑ n ∈ Finset.range N, f n x)
        Filter.atTop
        (nhds (∫ x in (0 : ℝ)..(Real.pi / 2), ∑' n : ℕ, f n x)) := hlim
    have h2 : (fun N : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2), ∑ n ∈ Finset.range N, f n x)
        = (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x) := by
      funext N
      exact hfin N
    rw [h2] at h1
    exact tendsto_nhds_unique h1 htsum_lim
  have hpoint : ∀ x : ℝ, (∑' n : ℕ, f n x)
      = -(x * Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) := by
    intro x
    have hgsum : Summable (fun n : ℕ =>
        r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)) := by
      have hle3 : ∀ n : ℕ, ‖r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)‖
          ≤ r ^ (n + 1) := by
        intro n
        have hcos : |Real.cos (2 * ((n : ℝ) + 1) * x)| ≤ 1 := Real.abs_cos_le_one _
        have hnn : (0 : ℝ) ≤ r ^ (n + 1) := pow_nonneg hr0 _
        have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
          have hle1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
            linarith
          calc (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 1 :=
                one_div_le_one_div_of_le (by norm_num) hle1
            _ = 1 := by simp
        calc ‖r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)‖
              = (r ^ (n + 1) * |Real.cos (2 * ((n : ℝ) + 1) * x)|) / ((n : ℝ) + 1) := by
                rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hnn,
                  abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
            _ ≤ (r ^ (n + 1) * 1) / ((n : ℝ) + 1) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_left hcos hnn
            _ = r ^ (n + 1) * (1 / ((n : ℝ) + 1)) := by ring
            _ ≤ r ^ (n + 1) * 1 := by
                apply mul_le_mul_of_nonneg_left h1 hnn
            _ = r ^ (n + 1) := by ring
      have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) := by
        have h : Summable (fun n : ℕ => r ^ n) :=
          summable_geometric_of_norm_lt_one (by
            rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
        have hshift := (summable_nat_add_iff 1).mpr h
        simpa [pow_add] using hshift
      exact Summable.of_norm_bounded hgeo hle3
    have hmul : (∑' n : ℕ, f n x)
        = x * (∑' n : ℕ, r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)) := by
      have hEq : (fun n : ℕ => f n x)
          = (fun (n : ℕ) => x *
            (r ^ (n + 1) * Real.cos (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1))) := by
        funext n
        unfold f
        ring
      rw [hEq]
      exact Summable.tsum_mul_left x hgsum
    have hpois := e22_poisson hr0 hr1 (x := x)
    rw [hmul, hpois]
    ring
  have hLHS : (∫ x in (0 : ℝ)..(Real.pi / 2), ∑' n : ℕ, f n x)
      = -∫ x in (0 : ℝ)..(Real.pi / 2),
        x * Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ := by
    have hEq : (fun x : ℝ => ∑' n : ℕ, f n x)
        = (fun x => -(x *
          Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)) := by
      funext x
      exact hpoint x
    rw [hEq, intervalIntegral.integral_neg]
  have hRHS : (∑' n : ℕ, ∫ x in (0 : ℝ)..(Real.pi / 2), f n x)
      = ∑' n : ℕ, r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 3)) := by
    congr 1
    funext n
    exact hterm_int n
  rw [hLHS, hRHS] at huniq
  have hneg : (∑' n : ℕ, r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 3)))
      = -(∑' n : ℕ, r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) / (4 * (((n : ℝ) + 1) ^ 3))) := by
    have hEq : (fun n : ℕ => r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) - 1) / (4 * (((n : ℝ) + 1) ^ 3)))
        = (fun n : ℕ => -(r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) / (4 * (((n : ℝ) + 1) ^ 3)))) := by
      funext n
      ring
    rw [hEq, tsum_neg]
  have hfinal : ∫ x in (0 : ℝ)..(Real.pi / 2),
        x * Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖
      = ∑' n : ℕ, r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) / (4 * (((n : ℝ) + 1) ^ 3)) := by
    rw [hneg] at huniq
    linarith [huniq]
  exact hfinal

private lemma e22_re_exp (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
  rw [e22_exp_I_mul_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

private lemma e22_im_exp (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))).im = Real.sin t := by
  rw [e22_exp_I_mul_ofReal]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

private lemma e22_norm_sub_exp_sq (r x : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ^ 2
      = 1 + r ^ 2 - 2 * r * Real.cos (2 * x) := by
  have hre : ((1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))).re
      = 1 - r * Real.cos (2 * x) := by
    rw [Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, e22_re_exp, e22_im_exp]
    ring
  have him : ((1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))).im
      = -(r * Real.sin (2 * x)) := by
    rw [Complex.sub_im, Complex.mul_im, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, e22_re_exp, e22_im_exp]
    ring
  have hnorm : ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ^ 2
      = ((1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))).re ^ 2
        + ((1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hnorm, hre, him]
  have hcs : Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq (2 * x)
  linear_combination (r ^ 2) * hcs

private lemma e22_norm_one_eq {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi / 2)) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ = 2 * Real.sin x := by
  have hsq := e22_norm_sub_exp_sq 1 x
  simp only [one_pow, mul_one] at hsq
  have hcos2 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    have h := Real.cos_two_mul' x
    have h2 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      have hs := Real.sin_sq_add_cos_sq x
      linarith [hs]
    rw [h, h2]
    ring
  have hsin_nn : 0 ≤ Real.sin x := by
    rw [Set.mem_Icc] at hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hpi := Real.pi_pos
      exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith))
  have hsq2 : ‖(1 : ℂ) - ((1 : ℝ) : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ^ 2
      = (2 * Real.sin x) ^ 2 := by
    rw [hsq, hcos2]
    ring
  have h1 : (1 : ℂ) - ((1 : ℝ) : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))
      = (1 : ℂ) - Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ)) := by
    simp
  rw [h1] at hsq2
  have hn1 : (0 : ℝ) ≤ ‖(1 : ℂ) - Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ :=
    norm_nonneg _
  have hn2 : (0 : ℝ) ≤ 2 * Real.sin x := by linarith [hsin_nn]
  have hsqrt := congrArg Real.sqrt hsq2
  rw [Real.sqrt_sq hn1, Real.sqrt_sq hn2] at hsqrt
  exact hsqrt

private lemma e22_abel_integrand_bound {r x : ℝ} (hr0 : (1 / 2 : ℝ) ≤ r)
    (hr1 : r ≤ 1) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖x * Real.log
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖‖ ≤
      |x * Real.log (Real.sin x)| + (3 / 2 * Real.log 2) * x := by
  have hpi := Real.pi_pos
  have hr_nonneg : 0 ≤ r := by linarith
  have hsin_pos : 0 < Real.sin x := by
    exact Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
  have hcos_two : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    have h := Real.cos_two_mul' x
    have hs := Real.sin_sq_add_cos_sq x
    nlinarith
  have hsq := e22_norm_sub_exp_sq r x
  have hsq' :
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ^ 2 =
        (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 := by
    rw [hsq, hcos_two]
    ring
  have hnorm_lower : Real.sin x ≤
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ := by
    have hsquares : Real.sin x ^ 2 ≤
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp
          (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ^ 2 := by
      rw [hsq']
      nlinarith [sq_nonneg (1 - r), sq_nonneg (Real.sin x)]
    nlinarith [norm_nonneg
      ((1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ)))]
  have hnorm_upper :
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ≤
          ‖(1 : ℂ)‖ +
            ‖(r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ :=
        norm_sub_le _ _
      _ = 1 + |r| := by
        rw [norm_one, norm_mul, e22_norm_exp_I_mul, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
      _ ≤ 2 := by rw [abs_of_nonneg hr_nonneg]; linarith
  have hnorm_pos : 0 <
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ :=
    hsin_pos.trans_le hnorm_lower
  have hlog_lower : Real.log (Real.sin x) ≤
      Real.log
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ :=
    Real.log_le_log hsin_pos hnorm_lower
  have hlog_upper :
      Real.log
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ≤
        Real.log 2 :=
    Real.log_le_log hnorm_pos hnorm_upper
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_abs :
      |Real.log
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖| ≤
        |Real.log (Real.sin x)| + 3 / 2 * Real.log 2 := by
    rw [abs_le]
    constructor
    · calc
        -(|Real.log (Real.sin x)| + 3 / 2 * Real.log 2) ≤
            Real.log (Real.sin x) := by
          have := neg_abs_le (Real.log (Real.sin x))
          nlinarith
        _ ≤ _ := hlog_lower
    · calc
        _ ≤ Real.log 2 := hlog_upper
        _ ≤ |Real.log (Real.sin x)| + 3 / 2 * Real.log 2 := by
          have := abs_nonneg (Real.log (Real.sin x))
          nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hx.1.le]
  calc
    x * |Real.log
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖| ≤
        x * (|Real.log (Real.sin x)| + 3 / 2 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlog_abs hx.1.le
    _ = x * |Real.log (Real.sin x)| + (3 / 2 * Real.log 2) * x := by ring

private lemma e22_abel_integrand_tendsto {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto
      (fun r : ℝ => x * Real.log
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)
      (nhdsWithin 1 (Set.Iic 1)) (nhds (x * Real.log (2 * Real.sin x))) := by
  have hinner : Continuous (fun r : ℝ =>
      (1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))) :=
    continuous_const.sub
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  have hnorm : Continuous (fun r : ℝ =>
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) :=
    hinner.norm
  have hxIcc : x ∈ Set.Icc 0 (Real.pi / 2) := ⟨hx.1.le, hx.2.le⟩
  have hnorm_one :
      ‖(1 : ℂ) - ((1 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ =
        2 * Real.sin x := by
    rw [Complex.ofReal_one, one_mul, e22_norm_one_eq hxIcc]
  have hnorm_ne :
      ‖(1 : ℂ) - ((1 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ ≠ 0 := by
    rw [hnorm_one]
    have hpi := Real.pi_pos
    exact ne_of_gt (mul_pos (by norm_num)
      (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])))
  have hlog : ContinuousAt (fun r : ℝ => Real.log
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) 1 :=
    hnorm.continuousAt.log hnorm_ne
  have hprod : ContinuousAt (fun r : ℝ => x * Real.log
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) 1 :=
    continuousAt_const.mul hlog
  have ht : ContinuousWithinAt (fun r : ℝ => x * Real.log
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)
      (Set.Iic 1) 1 :=
    hprod.continuousWithinAt
  change Filter.Tendsto
    (fun r : ℝ => x * Real.log
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)
    (nhdsWithin 1 (Set.Iic 1))
    (nhds (x * Real.log
      ‖(1 : ℂ) - ((1 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)) at ht
  rw [hnorm_one] at ht
  exact ht

private lemma e22_LHS_tendsto :
    Filter.Tendsto
      (fun r : ℝ => ∫ x in (0 : ℝ)..(Real.pi / 2),
        x * Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)
      (nhdsWithin 1 (Set.Iic 1))
      (nhds (∫ x in (0 : ℝ)..(Real.pi / 2), x * Real.log (2 * Real.sin x))) := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set F : ℝ → ℝ → ℝ := fun r x =>
    x * Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ with hF
  set f : ℝ → ℝ := fun x => x * Real.log (2 * Real.sin x) with hf
  set bound : ℝ → ℝ := fun x =>
    |x * Real.log (Real.sin x)| + (3 / 2 * Real.log 2) * x with hbound
  have hbound_int : IntervalIntegrable bound MeasureTheory.volume 0 (Real.pi / 2) := by
    have hA : IntervalIntegrable (fun x : ℝ => |x * Real.log (Real.sin x)|)
        MeasureTheory.volume 0 (Real.pi / 2) := by
      have hcont : ContinuousOn (fun x : ℝ => |x * Real.log (Real.sin x)|)
          (Set.Icc 0 (Real.pi / 2)) :=
        e22_ulogsin_continuousOn.abs
      exact hcont.intervalIntegrable_of_Icc hle
    have hC : IntervalIntegrable (fun x : ℝ => (3 / 2 * Real.log 2) * x)
        MeasureTheory.volume 0 (Real.pi / 2) :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hEq : bound = (fun x => |x * Real.log (Real.sin x)| + (3 / 2 * Real.log 2) * x) := rfl
    rw [hEq]
    exact hA.add hC
  have hF_meas : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iic 1),
      AEStronglyMeasurable (F r) (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have hpos : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iic 1), (0 : ℝ) ≤ r :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_ge_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hpos] with r hr hr0
    simp only [Set.mem_Iic] at hr
    by_cases hr1 : r < 1
    · have hcont : ContinuousOn (F r) (Set.Icc 0 (Real.pi / 2)) := by
        have hne : ∀ x : ℝ,
            (1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ)) ≠ 0 := by
          intro x
          have hnorm : ‖(r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ < 1 := by
            rw [norm_mul, e22_norm_exp_I_mul, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hr0]
            exact hr1
          intro hcon
          have hz1 : (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ)) = 1 := by
            linear_combination -hcon
          rw [hz1, norm_one] at hnorm
          linarith [hnorm]
        have hlogcont : ContinuousOn
            (fun x : ℝ => Real.log
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)
            (Set.Icc 0 (Real.pi / 2)) := by
          have hexp : Continuous (fun x : ℝ =>
              (1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))) :=
            continuous_const.sub (continuous_const.mul
              (Complex.continuous_exp.comp
                (continuous_const.mul (Complex.continuous_ofReal.comp
                  (continuous_const.mul continuous_id)))))
          have hnorm : Continuous (fun x : ℝ =>
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) :=
            hexp.norm
          exact Real.continuousOn_log.comp hnorm.continuousOn (fun x _ => by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact norm_ne_zero_iff.mpr (hne x))
        have hEq : F r = (fun x : ℝ => x *
            Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) := rfl
        rw [hEq]
        exact continuousOn_id.mul hlogcont
      exact (hcont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioo
    · push Not at hr1
      have hr_eq : r = 1 := le_antisymm hr hr1
      subst hr_eq
      have hcont : ContinuousOn (F 1) (Set.Icc 0 (Real.pi / 2)) := by
        have hEqOn : Set.EqOn (F 1) (fun x : ℝ => x * Real.log (2 * Real.sin x))
            (Set.Icc 0 (Real.pi / 2)) := by
          intro x hx
          change x * Real.log
              ‖(1 : ℂ) - ((1 : ℝ) : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖ =
            x * Real.log (2 * Real.sin x)
          rw [Complex.ofReal_one, one_mul, e22_norm_one_eq hx]
        have hTarget : ContinuousOn (fun x : ℝ => x * Real.log (2 * Real.sin x))
            (Set.Icc 0 (Real.pi / 2)) := by
          have hEqOn2 : Set.EqOn (fun x : ℝ => x * Real.log (2 * Real.sin x))
              (fun x : ℝ => x * Real.log 2 + x * Real.log (Real.sin x))
              (Set.Icc 0 (Real.pi / 2)) := by
            intro x hx
            by_cases hx0 : x = 0
            · subst hx0
              simp
            · have hsin : Real.sin x ≠ 0 := by
                rw [Set.mem_Icc] at hx
                have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
                exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos (by
                  have hpi := Real.pi_pos
                  linarith [hx.2]))
              have hlog : Real.log (2 * Real.sin x)
                  = Real.log 2 + Real.log (Real.sin x) :=
                Real.log_mul (by norm_num) hsin
              change x * Real.log (2 * Real.sin x)
                = x * Real.log 2 + x * Real.log (Real.sin x)
              rw [hlog]
              ring
          have hsum : ContinuousOn
              (fun x : ℝ => x * Real.log 2 + x * Real.log (Real.sin x))
              (Set.Icc 0 (Real.pi / 2)) :=
            (continuousOn_id.mul continuousOn_const).add e22_ulogsin_continuousOn
          exact hsum.congr hEqOn2
        exact hTarget.congr hEqOn
      exact (hcont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioo
  have hbound_integrable :
      Integrable bound
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have hIoc : Integrable bound
        (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.pi / 2))) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
        hbound_int).integrable
    rwa [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at hIoc
  have h_bound : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iic 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ‖F r x‖ ≤ bound x := by
    have hhalf : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iic 1), (1 / 2 : ℝ) ≤ r :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_ge_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hhalf] with r hr1 hr0
    simp only [Set.mem_Iic] at hr1
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact e22_abel_integrand_bound hr0 hr1 hx
  have h_lim : ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Set.Ioo 0 (Real.pi / 2))),
      Filter.Tendsto (fun r : ℝ => F r x) (nhdsWithin 1 (Set.Iic 1))
        (nhds (f x)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact e22_abel_integrand_tendsto hx
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    bound hF_meas h_bound hbound_integrable h_lim
  have hinterval (g : ℝ → ℝ) :
      (∫ x in (0 : ℝ)..(Real.pi / 2), g x) =
        ∫ x, g x ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, ite_eq_left hle, one_smul,
      Set.uIoc_of_le hle, MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  simpa only [hinterval] using hDCT

private def e22R (r : ℝ) (n : ℕ) : ℝ :=
  r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) / (4 * (((n : ℝ) + 1) ^ 3))

private lemma e22R_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    ‖e22R r n‖ ≤ 1 / (((n : ℝ) + 1) ^ 3) := by
  have hrpow : r ^ (n + 1) ≤ 1 := by
    calc
      r ^ (n + 1) ≤ 1 ^ (n + 1) := pow_le_pow_left₀ hr0 hr1 _
      _ = 1 := one_pow _
  have hrpow_nonneg : 0 ≤ r ^ (n + 1) := pow_nonneg hr0 _
  have hparity : |1 - (-1 : ℝ) ^ (n + 1)| ≤ 2 := by
    have hpow : |(-1 : ℝ) ^ (n + 1)| ≤ 1 := by rw [abs_pow]; simp
    calc
      |1 - (-1 : ℝ) ^ (n + 1)| ≤ |1| + |(-1 : ℝ) ^ (n + 1)| := abs_sub _ _
      _ ≤ 1 + 1 := by
        simpa only [abs_one, add_le_add_iff_left] using hpow
      _ = 2 := by norm_num
  have hden_pos : 0 < ((n : ℝ) + 1) ^ 3 := by positivity
  unfold e22R
  calc
    ‖r ^ (n + 1) * (1 - (-1 : ℝ) ^ (n + 1)) /
        (4 * (((n : ℝ) + 1) ^ 3))‖ =
        r ^ (n + 1) * |1 - (-1 : ℝ) ^ (n + 1)| /
          (4 * (((n : ℝ) + 1) ^ 3)) := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hrpow_nonneg,
        abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) * (((n : ℝ) + 1) ^ 3))]
    _ ≤ 1 * 2 / (4 * (((n : ℝ) + 1) ^ 3)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hrpow hparity (abs_nonneg _) zero_le_one
    _ ≤ 1 / (((n : ℝ) + 1) ^ 3) := by
      have hden_ne : ((n : ℝ) + 1) ^ 3 ≠ 0 := ne_of_gt hden_pos
      field_simp
      nlinarith

private lemma e22R_one_tsum :
    (∑' n : ℕ, e22R 1 n) = (1 / 2 : ℝ) * chapter9Chi3AtOne := by
  rw [chapter9Chi3AtOne_eq_entry21]
  have heven : (fun k : ℕ => e22R 1 (2 * k)) =
      (fun k : ℕ => (1 / 2 : ℝ) * chapter9Chi3Term k) := by
    funext k
    unfold e22R chapter9Chi3Term
    simp only [one_pow, one_mul, pow_add, pow_mul, neg_sq, one_pow, one_mul, pow_one]
    push_cast
    have h : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hodd : (fun k : ℕ => e22R 1 (2 * k + 1)) = fun _ => 0 := by
    funext k
    unfold e22R
    rw [show (2 * k + 1) + 1 = 2 * (k + 1) by omega]
    simp [pow_mul]
  have heven_sum : Summable (fun k : ℕ => e22R 1 (2 * k)) := by
    rw [heven]
    exact chi3_summable.mul_left (1 / 2 : ℝ)
  have hodd_sum : Summable (fun k : ℕ => e22R 1 (2 * k + 1)) := by
    rw [hodd]
    exact summable_zero
  have hsplit := tsum_even_add_odd heven_sum hodd_sum
  rw [heven, hodd, tsum_zero, add_zero,
    Summable.tsum_mul_left (1 / 2 : ℝ) chi3_summable] at hsplit
  exact hsplit.symm

private lemma e22R_tendsto :
    Filter.Tendsto (fun r : ℝ => ∑' n : ℕ, e22R r n)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 / 2 : ℝ) * chapter9Chi3AtOne)) := by
  have hpoint : ∀ n : ℕ, Filter.Tendsto (fun r : ℝ => e22R r n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (e22R 1 n)) := by
    intro n
    have hcont : ContinuousAt (fun r : ℝ => e22R r n) 1 := by
      unfold e22R
      fun_prop
    exact hcont.continuousWithinAt
  have hr_nonneg : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 ≤ r :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_ge_nhds (by norm_num))
  have hbound : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ n : ℕ, ‖e22R r n‖ ≤ 1 / (((n : ℝ) + 1) ^ 3) := by
    filter_upwards [self_mem_nhdsWithin, hr_nonneg] with r hr1 hr0
    simp only [Set.mem_Iio] at hr1
    exact fun n => e22R_bound hr0 hr1.le n
  have hlim := tendsto_tsum_of_dominated_convergence base3 hpoint hbound
  rwa [e22R_one_tsum] at hlim

private lemma e22_integral_ulog_two_sin :
    (∫ x in (0 : ℝ)..(Real.pi / 2), x * Real.log (2 * Real.sin x)) =
      (1 / 2 : ℝ) * chapter9Chi3AtOne := by
  have hleft := e22_LHS_tendsto.mono_left
    (nhdsWithin_mono 1 Set.Iio_subset_Iic_self)
  have hr_nonneg : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 ≤ r :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_ge_nhds (by norm_num))
  have heq : ∀ᶠ (r : ℝ) in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (∫ x in (0 : ℝ)..(Real.pi / 2),
        x * Real.log
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖) =
        ∑' n : ℕ, e22R r n := by
    filter_upwards [self_mem_nhdsWithin, hr_nonneg] with r hr1 hr0
    simp only [Set.mem_Iio] at hr1
    simpa only [e22R] using e22_poisson_integral hr0 hr1
  have hright : Filter.Tendsto
      (fun r : ℝ => ∫ x in (0 : ℝ)..(Real.pi / 2),
        x * Real.log
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (Complex.I * (((2 * x : ℝ)) : ℂ))‖)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 / 2 : ℝ) * chapter9Chi3AtOne)) :=
    e22R_tendsto.congr' (heq.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hleft hright

private lemma e22S_one_value :
    e22S 1 = Real.pi ^ 2 / 8 * Real.log 2 -
      (1 / 2 : ℝ) * chapter9Chi3AtOne := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hEq : Set.EqOn (fun x : ℝ => x * Real.log (2 * Real.sin x))
      (fun x : ℝ => x * Real.log 2 + x * Real.log (Real.sin x))
      (Set.uIcc 0 (Real.pi / 2)) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · have hsin : Real.sin x ≠ 0 := by
        have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2]))
      change x * Real.log (2 * Real.sin x) =
        x * Real.log 2 + x * Real.log (Real.sin x)
      rw [Real.log_mul (by norm_num) hsin]
      ring
  have hconst_int : IntervalIntegrable (fun x : ℝ => x * Real.log 2)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (continuous_id.mul continuous_const).intervalIntegrable _ _
  have hlog_int : IntervalIntegrable (fun x : ℝ => x * Real.log (Real.sin x))
      MeasureTheory.volume 0 (Real.pi / 2) :=
    e22_ulogsin_continuousOn.intervalIntegrable_of_Icc hle
  have hdecomp :
      (∫ x in (0 : ℝ)..(Real.pi / 2), x * Real.log (2 * Real.sin x)) =
        Real.pi ^ 2 / 8 * Real.log 2 +
          ∫ x in (0 : ℝ)..(Real.pi / 2), x * Real.log (Real.sin x) := by
    rw [intervalIntegral.integral_congr hEq,
      intervalIntegral.integral_add hconst_int hlog_int,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [e22_integral_ulog_two_sin] at hdecomp
  rw [e22S_one_eq_neg_integral_ulogsin]
  linarith [hdecomp]

private def e22M (u : ℝ) : ℝ :=
  arcsinIntegralSeries (Real.sin u) - u * Real.log (Real.sin u)

private lemma e22M_hasDerivAt {u : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt e22M (-Real.log (Real.sin u)) u := by
  have hnorm := e22_norm_ne_of_mem_Ioo hu
  have hF := (hasDerivAt_arcsinIntegralSeries hnorm.1 hnorm.2.2.1).comp u
    (Real.hasDerivAt_sin u)
  rw [e22_arcsin_sin_of_mem hu] at hF
  have hlog : HasDerivAt (fun u : ℝ => Real.log (Real.sin u))
      ((Real.sin u)⁻¹ * Real.cos u) u :=
    (Real.hasDerivAt_log hnorm.2.2.1).comp u (Real.hasDerivAt_sin u)
  have hmul := (hasDerivAt_id' u).mul hlog
  unfold e22M
  refine (hF.sub hmul).congr_deriv ?_
  ring

private lemma e22M_continuousOn :
    ContinuousOn e22M (Set.Icc 0 (Real.pi / 2)) := by
  have hFsin : ContinuousOn (fun u : ℝ => arcsinIntegralSeries (Real.sin u))
      (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_arcsinIntegralSeries.comp Real.continuous_sin.continuousOn
      (fun u _ => (e22_sin_cos_mem_Icc u).1)
  unfold e22M
  exact hFsin.sub e22_ulogsin_continuousOn

private lemma e22F_one_value :
    arcsinIntegralSeries 1 = Real.pi / 2 * Real.log 2 := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hlog_int : IntervalIntegrable (fun u : ℝ => Real.log (Real.sin u))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    change IntervalIntegrable (Real.log ∘ Real.sin)
      MeasureTheory.volume 0 (Real.pi / 2)
    exact intervalIntegrable_log_sin
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    e22M_continuousOn (fun u hu => e22M_hasDerivAt hu) hlog_int.neg
  have hMpi : e22M (Real.pi / 2) = arcsinIntegralSeries 1 := by
    unfold e22M
    rw [Real.sin_pi_div_two, Real.log_one]
    ring
  have hM0 : e22M 0 = 0 := by
    unfold e22M
    rw [Real.sin_zero, arcsinIntegralSeries_zero]
    ring
  rw [hMpi, hM0, sub_zero] at hFTC
  calc
    arcsinIntegralSeries 1 = ∫ u in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin u) := hFTC.symm
    _ = -(∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin u)) := by
      rw [intervalIntegral.integral_neg]
    _ = Real.pi / 2 * Real.log 2 := by
      rw [integral_log_sin_zero_pi_div_two]
      ring

private lemma e22H_zero : e22H 0 = 0 := by
  unfold e22H
  rw [Real.sin_zero, Real.cos_zero, e22S_zero, e22S_one_value, e22F_one_value]
  norm_num
  rw [e22S_zero]
  ring

private lemma e22H_eq_zero (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    e22H x = 0 := by
  have hcont : ContinuousOn e22H (Set.Icc 0 x) := by
    refine e22H_continuousOn.mono ?_
    intro u hu
    exact ⟨hu.1, hu.2.trans hx⟩
  have hderiv : ∀ u ∈ Set.Ioo 0 x, HasDerivAt e22H 0 u := by
    intro u hu
    exact e22H_hasDerivAt_zero ⟨hu.1, hu.2.trans_le hx⟩
  have hint : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 x :=
    continuous_const.intervalIntegrable 0 x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hcont hderiv hint
  simpa [e22H_zero] using hFTC.symm

/-- **Entry 22 of Chapter 9 of Ramanujan's notebooks.** For real $u$ and $k \ge 0$ let
$T_k(u) = \frac{2^{2k} (k!)^2 \sin^{2k+2} u}{(2k+1)! \, (2k+2)^2}$. Let $x$ be real with
$0 \le x \le \pi/4$. Then $2 \cos x > 0$, the series $\sum_{j \ge 0} \frac{1}{(2j+1)^3}$,
$\sum_{k \ge 0} \bigl(T_k(x) + T_k(\pi/2 - x)\bigr)$,
$\sum_{k \ge 0} \frac{\binom{2k}{k} \cos^{2k+1} x}{2^{2k} (2k+1)^2}$ and $\sum_{k \ge 0} T_k(2x)$
converge absolutely, and

$$
\sum_{k \ge 0} \bigl(T_k(x) + T_k(\pi/2 - x)\bigr) = -\frac{\pi^2}{8} \log(2 \cos x) +
\frac{\pi}{2} \sum_{k \ge 0} \frac{\binom{2k}{k} \cos^{2k+1} x}{2^{2k} (2k+1)^2} +
\frac{1}{4} \sum_{k \ge 0} T_k(2x) - \frac{1}{2} \sum_{j \ge 0} \frac{1}{(2j+1)^3}.
$$

Proof: Differentiate the factorial and central-binomial series termwise, reduce
the logarithmic integral by Abel's limit and dominated convergence, and finish
by the fundamental theorem of calculus. This follows Berndt's Entries 20–23 and
Lehmer's arcsine series.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9,
Entry 22, pp. 270–271. The printed range `0 ≤ x ≤ π / 2` is false. This target
uses `0 ≤ x ≤ π / 4`, the range supported by the source proof's substitution
of `2 * x` into Entry 20; the endpoint remains an explicit proof obligation.
-/
theorem ramanujan_part1_ch9_entry22_chudnovsky (x : ℝ)
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < 2 * Real.cos x ∧
      Summable chapter9Chi3Term ∧
      Summable (chapter9Entry22LeftTerm x) ∧
      Summable (chapter9Entry22CentralTerm x) ∧
      Summable (chapter9Entry23FactorialTerm (2 * x)) ∧
      (∑' k : ℕ, chapter9Entry22LeftTerm x k) =
        -(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x) +
          Real.pi / 2 * ∑' k : ℕ, chapter9Entry22CentralTerm x k +
          (1 / 4 : ℝ) *
            ∑' k : ℕ, chapter9Entry23FactorialTerm (2 * x) k -
          (1 / 2 : ℝ) * chapter9Chi3AtOne := by
  have hpos : 0 < 2 * Real.cos x := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
    have hc := Real.cos_pos_of_mem_Ioo hxmem
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hfac_x : Summable (chapter9Entry23FactorialTerm x) :=
    factorial_summable x (by
      rw [abs_of_nonneg hx0]
      linarith)
  have hfac_compl :
      Summable (chapter9Entry23FactorialTerm (Real.pi / 2 - x)) :=
    factorial_summable (Real.pi / 2 - x) (by
      rw [abs_of_nonneg (by linarith)]
      linarith)
  have hfac_two_x : Summable (chapter9Entry23FactorialTerm (2 * x)) :=
    factorial_summable (2 * x) (by
      rw [abs_of_nonneg (by linarith)]
      linarith)
  have hleft : Summable (chapter9Entry22LeftTerm x) := hfac_x.add hfac_compl
  refine ⟨hpos, chi3_summable, hleft, central_summable x, hfac_two_x, ?_⟩
  have hsplit : (∑' k : ℕ, chapter9Entry22LeftTerm x k)
      = (∑' k : ℕ, chapter9Entry23FactorialTerm x k)
        + (∑' k : ℕ, chapter9Entry23FactorialTerm (Real.pi / 2 - x) k) :=
    Summable.tsum_add hfac_x hfac_compl
  rw [hsplit]
  have hScos : e22S (Real.cos x) =
      ∑' k : ℕ, chapter9Entry23FactorialTerm (Real.pi / 2 - x) k := by
    rw [← Real.sin_pi_div_two_sub x]
    exact e22S_sin_eq_tsum _
  have hH := e22H_eq_zero x hx0 hx
  unfold e22H at hH
  rw [e22S_sin_eq_tsum x, hScos, e22F_cos_eq_tsum x,
    e22S_sin_eq_tsum (2 * x)] at hH
  exact sub_eq_zero.mp hH

end
end Entry22Chudnovsky
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
