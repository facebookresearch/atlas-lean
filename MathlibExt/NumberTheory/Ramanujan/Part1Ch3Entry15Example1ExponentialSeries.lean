/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry14Cor1Catalanpowerseries

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

The main theorem proves Entry 15, Example 1, evaluating Ramanujan's exponential series as
`2 ^ m` for `0 < n ≤ 2`.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15Example1ExponentialSeries

private lemma expSeries_hasSum_m_zero (n : ℝ) :
    HasSum (fun k : ℕ =>
      if k = 0 then (1 : ℝ)
      else ((0 : ℝ) * ∏ j ∈ Finset.range (k - 1), ((0 : ℝ) + (k : ℝ) * n - ((j : ℝ) + 1))) /
        ((2 : ℝ) ^ ((k : ℝ) * n) * (Nat.factorial k : ℝ))) ((2 : ℝ) ^ (0 : ℝ)) := by
  rw [Real.rpow_zero]
  have h : (fun k : ℕ =>
      if k = 0 then (1 : ℝ)
      else ((0 : ℝ) * ∏ j ∈ Finset.range (k - 1), ((0 : ℝ) + (k : ℝ) * n - ((j : ℝ) + 1))) /
        ((2 : ℝ) ^ ((k : ℝ) * n) * (Nat.factorial k : ℝ)))
      = (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
    funext k
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, zero_mul]
  rw [h]
  exact hasSum_ite_eq 0 1

private noncomputable def abelB (m n : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    (m * ∏ i ∈ Finset.range k, (m + (k + 1 : ℕ) * n - 1 - i))
      / (Nat.factorial (k + 1) : ℝ)

private noncomputable def gchoose (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    (∏ i ∈ Finset.range (k + 1), (r - i)) / (Nat.factorial (k + 1) : ℝ)

private lemma abelB_zero (m n : ℝ) : abelB m n 0 = 1 := rfl

private lemma abelB_one (m n : ℝ) : abelB m n 1 = m := by
  simp only [abelB, Finset.range_zero, Finset.prod_empty, zero_add,
    Nat.factorial_one, Nat.cast_one, mul_one, div_one]

private lemma gchoose_zero (r : ℝ) : gchoose r 0 = 1 := rfl

private lemma abelB_succ (m n : ℝ) (k : ℕ) :
    abelB m n (k + 1)
      = (m * ∏ i ∈ Finset.range k, (m + ((k + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ)))
        / (Nat.factorial (k + 1) : ℝ) := rfl

private lemma gchoose_succ (r : ℝ) (k : ℕ) :
    gchoose r (k + 1)
      = (∏ i ∈ Finset.range (k + 1), (r - (i : ℝ)))
        / (Nat.factorial (k + 1) : ℝ) := rfl

private lemma expSeries_gchoose_eq_ring_choose (r : ℝ) (k : ℕ) :
    gchoose r k = Ring.choose r k := by
  cases k with
  | zero => simp [gchoose_zero]
  | succ j =>
    rw [gchoose_succ, Ring.choose_eq_smul]
    simp only [smul_eq_mul, inv_mul_eq_div]
    have hprod : ∀ q : ℕ, (descPochhammer ℤ q).smeval r =
        ∏ i ∈ Finset.range q, (r - (i : ℝ)) := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih,
          Finset.prod_range_succ]
        simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
          Polynomial.smeval_natCast, pow_one, pow_zero, nsmul_one]
    rw [hprod (j + 1)]

private lemma expSeries_gchoose_succ_eq_mul (r : ℝ) (k : ℕ) :
    gchoose r (k + 1) = gchoose r k * (r - k) / (k + 1) := by
  cases k with
  | zero => simp [gchoose_zero, gchoose_succ]
  | succ j =>
    rw [gchoose_succ, gchoose_succ, Finset.prod_range_succ, Nat.factorial_succ]
    push_cast
    have hfac : (Nat.factorial (j + 1) : ℝ) ≠ 0 := by positivity
    have hj : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp

private lemma expSeries_gchoose_succ_eq_mul_pred (r : ℝ) (k : ℕ) :
    gchoose r (k + 1) = r / (k + 1) * gchoose (r - 1) k := by
  cases k with
  | zero => simp [gchoose_zero, gchoose_succ]
  | succ j =>
    rw [gchoose_succ, gchoose_succ, Finset.prod_range_succ']
    simp only [Nat.cast_zero, sub_zero]
    have hprod : (∏ x ∈ Finset.range (j + 1), (r - ((x + 1 : ℕ) : ℝ))) =
        ∏ x ∈ Finset.range (j + 1), (r - 1 - (x : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [hprod, Nat.factorial_succ]
    push_cast
    have hfac : (Nat.factorial (j + 1) : ℝ) ≠ 0 := by positivity
    have hj : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp

private lemma expSeries_abs_gchoose_le_one (k : ℕ) (r : ℝ)
    (hr0 : -1 ≤ r) (hrk : r ≤ k) :
    |gchoose r (k + 1)| ≤ 1 := by
  induction k generalizing r with
  | zero =>
    have h : gchoose r 1 = r := by simp [gchoose]
    rw [h, abs_le]
    constructor
    · exact hr0
    · norm_num at hrk
      exact hrk.trans zero_le_one
  | succ k ih =>
    by_cases hr : r ≤ k
    · rw [expSeries_gchoose_succ_eq_mul, abs_div, abs_mul]
      have hgc := ih r hr0 hr
      have hdiff : |r - ((k + 1 : ℕ) : ℝ)| ≤ ((k + 1 : ℕ) : ℝ) + 1 := by
        have hnonpos : r - ((k + 1 : ℕ) : ℝ) ≤ 0 := by
          push_cast at hr ⊢
          linarith
        rw [abs_of_nonpos hnonpos]
        push_cast
        linarith
      have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
      rw [abs_of_pos hden]
      apply (div_le_one hden).2
      calc
        |gchoose r (k + 1)| * |r - ((k + 1 : ℕ) : ℝ)|
            ≤ 1 * (((k + 1 : ℕ) : ℝ) + 1) :=
              mul_le_mul hgc hdiff (abs_nonneg _) zero_le_one
        _ = ((k + 1 : ℕ) : ℝ) + 1 := one_mul _
    · rw [expSeries_gchoose_succ_eq_mul_pred, abs_mul, abs_div]
      have hrk' : (-1 : ℝ) ≤ r - 1 := by linarith
      have hrupper : r - 1 ≤ k := by
        push_cast at hrk ⊢
        linarith
      have hgc := ih (r - 1) hrk' hrupper
      have hrabs : |r| ≤ (k + 1 : ℕ) := by
        rw [abs_le]
        constructor
        · linarith
        · exact hrk
      have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
      rw [abs_of_pos hden]
      calc
        |r| / (((k + 1 : ℕ) : ℝ) + 1) * |gchoose (r - 1) (k + 1)|
            ≤ 1 * 1 := by
              apply mul_le_mul
              · exact (div_le_one hden).2 (hrabs.trans (by linarith))
              · exact hgc
              · exact abs_nonneg _
              · positivity
        _ = 1 := by norm_num

private lemma expSeries_abelB_n_one_eq_choose (m : ℝ) (k : ℕ) :
    abelB m 1 k = Ring.choose (m + k - 1) k := by
  cases k with
  | zero => simp [abelB_zero]
  | succ j =>
    rw [← expSeries_gchoose_eq_ring_choose, gchoose_succ]
    simp only [abelB]
    rw [Finset.prod_range_succ]
    have hprod : (∏ i ∈ Finset.range j,
        (m + ((j + 1 : ℕ) : ℝ) * 1 - 1 - (i : ℝ))) =
        ∏ i ∈ Finset.range j, (m + ((j + 1 : ℕ) : ℝ) - 1 - (i : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [hprod]
    push_cast
    ring

private lemma expSeries_hasSum_abelB_n_one (m : ℝ) :
    HasSum (fun k : ℕ => abelB m 1 k * (1 / 2 : ℝ) ^ k) ((2 : ℝ) ^ m) := by
  have hmem : (1 / 2 : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    norm_num [Real.norm_eq_abs]
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero m).hasSum hmem
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at h
  have hfun : (fun k : ℕ => Ring.choose (m + (k : ℝ) - 1) k * (1 / 2 : ℝ) ^ k) =
      fun k : ℕ => abelB m 1 k * (1 / 2 : ℝ) ^ k := by
    funext k
    rw [expSeries_abelB_n_one_eq_choose]
  rw [hfun] at h
  convert h using 1
  norm_num [Real.div_rpow]

private lemma expSeries_mul_abelB_eq_mul_gchoose (m n : ℝ) (k : ℕ) :
    (m + n * (k : ℝ)) * abelB m n k = m * gchoose (m + n * (k : ℝ)) k := by
  cases k with
  | zero => simp [abelB_zero, gchoose_zero]
  | succ j =>
    have hprod : ∏ i ∈ Finset.range j,
          (m + ((j + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ))
        = ∏ i ∈ Finset.range j,
          (m + n * ((j + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [abelB_succ, gchoose_succ, Finset.prod_range_succ']
    simp only [Nat.cast_zero, sub_zero]
    rw [hprod]
    ring

private lemma expSeries_summable_norm_low (m n x : ℝ)
    (hn0 : 0 < n) (hn1 : n < 1) (hx : |x| < 1) :
    Summable (fun k : ℕ => ‖abelB m n k * x ^ k‖) := by
  let d : ℝ := min n (1 - n)
  have hd : 0 < d := lt_min hn0 (sub_pos.mpr hn1)
  obtain ⟨K, hK⟩ := exists_nat_gt ((|m| + 1) / d)
  have hlarge : ∀ k : ℕ, K ≤ k → |abelB m n k| ≤ |m| := by
    intro k hk
    have hbase : |m| + 1 < d * (k : ℝ) := by
      have hfirst : |m| + 1 < d * (K : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hd).mp hK
      have hcast : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      exact hfirst.trans_le (mul_le_mul_of_nonneg_left hcast hd.le)
    have hdn : d ≤ n := min_le_left _ _
    have hdsub : d ≤ 1 - n := min_le_right _ _
    have hmk_lower : -|m| ≤ m := neg_abs_le m
    have hmk_upper : m ≤ |m| := le_abs_self m
    let r : ℝ := m + n * (k : ℝ)
    have hr1 : 1 ≤ r := by
      simp only [r]
      nlinarith [mul_le_mul_of_nonneg_right hdn (Nat.cast_nonneg k)]
    have hrupper : r ≤ (k : ℝ) - 1 := by
      simp only [r]
      nlinarith [mul_le_mul_of_nonneg_right hdsub (Nat.cast_nonneg k)]
    have hkone : 1 ≤ k := by
      have : (1 : ℝ) ≤ (k : ℝ) := by linarith
      exact_mod_cast this
    have hrupper' : r ≤ ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hkone]
      simpa using hrupper
    have hg := expSeries_abs_gchoose_le_one (k - 1) r (by linarith) hrupper'
    have hksucc : k - 1 + 1 = k := Nat.sub_add_cancel hkone
    rw [hksucc] at hg
    have hb := expSeries_mul_abelB_eq_mul_gchoose m n k
    have habs := congrArg abs hb
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    change |r * abelB m n k| = |m * gchoose r k| at habs
    rw [abs_mul, abs_mul, abs_of_pos hrpos] at habs
    calc
      |abelB m n k| ≤ r * |abelB m n k| := by
        nlinarith [abs_nonneg (abelB m n k)]
      _ = |m| * |gchoose r k| := habs
      _ ≤ |m| * 1 := mul_le_mul_of_nonneg_left hg (abs_nonneg m)
      _ = |m| := mul_one _
  have hgeo : Summable (fun k : ℕ => |m| * |x| ^ k) := by
    apply Summable.mul_left
    exact summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using hx)
  apply hgeo.of_norm_bounded_eventually_nat
  refine Filter.eventually_atTop.2 ⟨K, ?_⟩
  intro k hk
  simp only [norm_mul, Real.norm_eq_abs, norm_pow, abs_abs]
  exact mul_le_mul_of_nonneg_right (hlarge k hk) (pow_nonneg (abs_nonneg x) k)

private lemma abelB_rec (m n : ℝ) (k : ℕ) :
    abelB m n (k + 1) = abelB (m - 1) n (k + 1) + abelB (m + n - 1) n k := by
  cases k with
  | zero =>
    change abelB m n 1 = abelB (m - 1) n 1 + abelB (m + n - 1) n 0
    simp only [abelB_zero, abelB_one]
    ring
  | succ j =>
    have hP0 : ∏ i ∈ Finset.range (j + 1),
          (m + (((j + 1 + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ))
        = (m + (((j + 1 + 1 : ℕ)) : ℝ) * n - 1)
          * ∏ i ∈ Finset.range j, (m + (((j + 1 + 1 : ℕ)) : ℝ) * n - 2 - (i : ℝ)) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · rw [Nat.cast_zero, sub_zero]
      · apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
    have hP1 : ∏ i ∈ Finset.range (j + 1),
          (m - 1 + (((j + 1 + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ))
        = (∏ i ∈ Finset.range j, (m + (((j + 1 + 1 : ℕ)) : ℝ) * n - 2 - (i : ℝ)))
          * (m + (((j + 1 + 1 : ℕ)) : ℝ) * n - (j + 1) - 1) := by
      rw [Finset.prod_range_succ]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        ring
      · push_cast
        ring
    have hP2 : ∏ i ∈ Finset.range j,
          (m + n - 1 + (((j + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ))
        = ∏ i ∈ Finset.range j, (m + (((j + 1 + 1 : ℕ)) : ℝ) * n - 2 - (i : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [abelB_succ, abelB_succ, abelB_succ, hP0, hP1, hP2]
    have hfact :
        (Nat.factorial (j + 1 + 1) : ℝ)
          = ((j + 1 + 1 : ℕ) : ℝ) * (Nat.factorial (j + 1) : ℝ) := by
      have h := Nat.factorial_succ (j + 1)
      have hc : ((Nat.factorial (j + 1 + 1) : ℕ) : ℝ)
          = ((((j + 1 + 1 : ℕ))) : ℝ) * ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
      exact hc
    have hne : (Nat.factorial (j + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hKne : (((j + 1 + 1 : ℕ)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (j + 1)
    rw [hfact]
    field_simp
    push_cast
    ring

private lemma gchoose_pascal (r : ℝ) (t : ℕ) :
    gchoose r (t + 1) = gchoose (r - 1) (t + 1) + gchoose (r - 1) t := by
  cases t with
  | zero =>
    change gchoose r 1 = gchoose (r - 1) 1 + gchoose (r - 1) 0
    simp only [gchoose_zero]
    have h1 : gchoose r 1 = r := by
      simp only [gchoose, zero_add, Finset.range_one, Finset.prod_singleton,
        Nat.factorial_one, Nat.cast_one, Nat.cast_zero, div_one, sub_zero]
    have h2 : gchoose (r - 1) 1 = r - 1 := by
      simp only [gchoose, zero_add, Finset.range_one, Finset.prod_singleton,
        Nat.factorial_one, Nat.cast_one, Nat.cast_zero, div_one, sub_zero]
    rw [h1, h2]
    ring
  | succ s =>
    have hQ0 : ∏ i ∈ Finset.range (s + 1 + 1), (r - (i : ℝ))
        = r * ∏ i ∈ Finset.range (s + 1), (r - 1 - (i : ℝ)) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · simp only [Nat.cast_zero, sub_zero]
      · apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
    have hQ1 : ∏ i ∈ Finset.range (s + 1 + 1), (r - 1 - (i : ℝ))
        = (∏ i ∈ Finset.range (s + 1), (r - 1 - (i : ℝ)))
          * (r - 1 - ((s + 1 : ℕ) : ℝ)) := by
      rw [Finset.prod_range_succ]
    have hfact :
        (Nat.factorial (s + 1 + 1) : ℝ)
          = ((s + 1 + 1 : ℕ) : ℝ) * (Nat.factorial (s + 1) : ℝ) := by
      have h := Nat.factorial_succ (s + 1)
      have hc : ((Nat.factorial (s + 1 + 1) : ℕ) : ℝ)
          = ((((s + 1 + 1 : ℕ))) : ℝ) * ((Nat.factorial (s + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
      exact hc
    have hne : (Nat.factorial (s + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hKne : (((s + 1 + 1 : ℕ)) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (s + 1)
    rw [gchoose_succ, gchoose_succ, gchoose_succ, hQ0, hQ1, hfact]
    field_simp
    push_cast
    ring

private lemma abelB_zero_succ (n : ℝ) (k : ℕ) : abelB 0 n (k + 1) = 0 := by
  simp only [abelB_succ, zero_mul, zero_div]

private lemma hagenRothe_nat (N T : ℕ) (R : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.range (T + 1),
        abelB (M : ℝ) (N : ℝ) k * gchoose (R - (M : ℝ) - (N : ℝ) * (k : ℝ)) (T - k)
      = gchoose R T := by
  induction T generalizing R M with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Nat.sub_zero, abelB_zero,
      gchoose_zero, mul_one]
  | succ t ih_t =>
    induction M generalizing R with
    | zero =>
      have h0 : abelB ((0 : ℕ) : ℝ) (N : ℝ) 0
            * gchoose (R - ((0 : ℕ) : ℝ) - (N : ℝ) * ((0 : ℕ) : ℝ)) (t + 1 - 0)
          = gchoose R (t + 1) := by
        simp only [abelB_zero, Nat.cast_zero, Nat.sub_zero, mul_zero,
          sub_zero, one_mul]
      have hS : ∀ j ∈ Finset.range (t + 1),
          abelB ((0 : ℕ) : ℝ) (N : ℝ) (j + 1)
            * gchoose (R - ((0 : ℕ) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
              (t + 1 - (j + 1)) = 0 := by
        intro j _
        simp only [Nat.cast_zero, abelB_zero_succ, zero_mul]
      have hsplit : ∑ k ∈ Finset.range (t + 1 + 1),
            abelB ((0 : ℕ) : ℝ) (N : ℝ) k
              * gchoose (R - ((0 : ℕ) : ℝ) - (N : ℝ) * (k : ℝ)) (t + 1 - k)
          = (∑ j ∈ Finset.range (t + 1),
              abelB ((0 : ℕ) : ℝ) (N : ℝ) (j + 1)
                * gchoose (R - ((0 : ℕ) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                  (t + 1 - (j + 1)))
            + abelB ((0 : ℕ) : ℝ) (N : ℝ) 0
              * gchoose (R - ((0 : ℕ) : ℝ) - (N : ℝ) * ((0 : ℕ) : ℝ))
                (t + 1 - 0) := by
        rw [Finset.sum_range_succ']
      rw [hsplit]
      simp only [Finset.sum_eq_zero hS, zero_add]
      exact h0
    | succ m ih_m =>
      have hM1 : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by
        push_cast
        ring
      have hMN : (((m + 1 : ℕ)) : ℝ) + (N : ℝ) - 1 = ((m + N : ℕ) : ℝ) := by
        push_cast
        ring
      have hsplit : ∑ k ∈ Finset.range (t + 1 + 1),
            abelB (((m + 1 : ℕ)) : ℝ) (N : ℝ) k
              * gchoose (R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * (k : ℝ))
                (t + 1 - k)
          = (∑ j ∈ Finset.range (t + 1),
              abelB (((m + 1 : ℕ)) : ℝ) (N : ℝ) (j + 1)
                * gchoose
                  (R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                  (t + 1 - (j + 1)))
            + abelB (((m + 1 : ℕ)) : ℝ) (N : ℝ) 0
              * gchoose (R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((0 : ℕ) : ℝ))
                (t + 1 - 0) := by
        rw [Finset.sum_range_succ']
      have h0eq : abelB (((m + 1 : ℕ)) : ℝ) (N : ℝ) 0
            * gchoose (R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((0 : ℕ) : ℝ))
              (t + 1 - 0)
          = gchoose (R - 1 - (m : ℝ)) (t + 1) := by
        simp only [abelB_zero, Nat.cast_zero, Nat.sub_zero, mul_zero,
          sub_zero, one_mul]
        congr 1
        push_cast
        ring
      have h1eq : ∀ j ∈ Finset.range (t + 1),
          abelB (((m + 1 : ℕ)) : ℝ) (N : ℝ) (j + 1)
            * gchoose (R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
              (t + 1 - (j + 1))
          = abelB (m : ℝ) (N : ℝ) (j + 1)
              * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                (t - j)
            + abelB ((m + N : ℕ) : ℝ) (N : ℝ) j
              * gchoose (R - 1 - ((m + N : ℕ) : ℝ) - (N : ℝ) * (j : ℝ))
                (t - j) := by
        intro j _
        have hrec := abelB_rec (((m + 1 : ℕ)) : ℝ) (N : ℝ) j
        have hm1 : (((m + 1 : ℕ)) : ℝ) - 1 = (m : ℝ) := by
          push_cast
          ring
        rw [hm1, hMN] at hrec
        have hsub : t + 1 - (j + 1) = t - j := by
          omega
        have hr1 : R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ)
            = R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        have hr2 : R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ)
            = R - 1 - ((m + N : ℕ) : ℝ) - (N : ℝ) * (j : ℝ) := by
          push_cast
          ring
        rw [hrec, add_mul]
        congr 1
        · rw [hr1, hsub]
        · rw [hr2, hsub]
      have hsum1 : ∑ j ∈ Finset.range (t + 1),
            abelB (((m + 1 : ℕ)) : ℝ) (N : ℝ) (j + 1)
              * gchoose (R - (((m + 1 : ℕ)) : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                (t + 1 - (j + 1))
          = (∑ j ∈ Finset.range (t + 1),
              abelB (m : ℝ) (N : ℝ) (j + 1)
                * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                  (t - j))
            + ∑ j ∈ Finset.range (t + 1),
              abelB ((m + N : ℕ) : ℝ) (N : ℝ) j
                * gchoose (R - 1 - ((m + N : ℕ) : ℝ) - (N : ℝ) * (j : ℝ))
                  (t - j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact h1eq j hj
      have hB : ∑ j ∈ Finset.range (t + 1),
            abelB ((m + N : ℕ) : ℝ) (N : ℝ) j
              * gchoose (R - 1 - ((m + N : ℕ) : ℝ) - (N : ℝ) * (j : ℝ)) (t - j)
          = gchoose (R - 1) t :=
        ih_t (R - 1) (m + N)
      have hA : (∑ j ∈ Finset.range (t + 1),
              abelB (m : ℝ) (N : ℝ) (j + 1)
                * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                  (t - j))
            + gchoose (R - 1 - (m : ℝ)) (t + 1)
          = gchoose (R - 1) (t + 1) := by
        have hmR := ih_m (R - 1)
        have hsplit2 : ∑ k ∈ Finset.range (t + 1 + 1),
              abelB (m : ℝ) (N : ℝ) k
                * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * (k : ℝ)) (t + 1 - k)
            = (∑ j ∈ Finset.range (t + 1),
                abelB (m : ℝ) (N : ℝ) (j + 1)
                  * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                    (t + 1 - (j + 1)))
              + abelB (m : ℝ) (N : ℝ) 0
                * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((0 : ℕ) : ℝ))
                  (t + 1 - 0) := by
          rw [Finset.sum_range_succ']
        have h0b : abelB (m : ℝ) (N : ℝ) 0
              * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((0 : ℕ) : ℝ))
                (t + 1 - 0)
            = gchoose (R - 1 - (m : ℝ)) (t + 1) := by
          simp only [abelB_zero, Nat.cast_zero, Nat.sub_zero, mul_zero,
            sub_zero, one_mul]
        have hsub2 : ∀ j ∈ Finset.range (t + 1),
            abelB (m : ℝ) (N : ℝ) (j + 1)
              * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                (t + 1 - (j + 1))
            = abelB (m : ℝ) (N : ℝ) (j + 1)
              * gchoose (R - 1 - (m : ℝ) - (N : ℝ) * ((j + 1 : ℕ) : ℝ))
                (t - j) := by
          intro j _
          have hsub : t + 1 - (j + 1) = t - j := by
            omega
          rw [hsub]
        rw [hmR] at hsplit2
        rw [Finset.sum_congr rfl hsub2] at hsplit2
        rw [h0b] at hsplit2
        linarith
      rw [hsplit, hsum1, h0eq]
      have hpas := gchoose_pascal R t
      linarith [hA, hB, hpas]

private noncomputable def BpolyM (N k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.X * (∏ i ∈ Finset.range j,
      (Polynomial.X + Polynomial.C (((j + 1 : ℕ) : ℝ) * (N : ℝ) - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

private lemma BpolyM_eval (N k : ℕ) (M : ℝ) :
    Polynomial.eval M (BpolyM N k) = abelB M (N : ℝ) k := by
  cases k with
  | zero =>
    simp only [BpolyM, abelB_zero, Polynomial.eval_one]
  | succ j =>
    simp only [BpolyM, abelB_succ, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C,
      div_eq_mul_inv]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring

private noncomputable def GpolyM (N T : ℕ) (R : ℝ) (k : ℕ) :
    Polynomial ℝ :=
  (∏ i ∈ Finset.range (T - k),
    (Polynomial.C (R - (N : ℝ) * (k : ℝ) - (i : ℝ)) - Polynomial.X))
    * Polynomial.C (((Nat.factorial (T - k) : ℝ))⁻¹)

private lemma GpolyM_eval (N T : ℕ) (R M : ℝ) (k : ℕ) :
    Polynomial.eval M (GpolyM N T R k)
      = gchoose (R - M - (N : ℝ) * (k : ℝ)) (T - k) := by
  cases hTK : T - k with
  | zero =>
    simp only [GpolyM, hTK, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, inv_one, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_C, mul_one, gchoose_zero]
  | succ j =>
    have hg : gchoose (R - M - (N : ℝ) * (k : ℝ)) (j + 1)
        = (∏ i ∈ Finset.range (j + 1), (R - M - (N : ℝ) * (k : ℝ) - (i : ℝ)))
          / (Nat.factorial (j + 1) : ℝ) := by
      have h := gchoose_succ (R - M - (N : ℝ) * (k : ℝ)) j
      exact h
    simp only [GpolyM]
    rw [hTK]
    simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv, hg]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring

private lemma hagenRothe_realM (N T : ℕ) (R M : ℝ) :
    ∑ k ∈ Finset.range (T + 1),
        abelB M (N : ℝ) k * gchoose (R - M - (N : ℝ) * (k : ℝ)) (T - k)
      = gchoose R T := by
  set P : Polynomial ℝ :=
    ∑ k ∈ Finset.range (T + 1), BpolyM N k * GpolyM N T R k with hP
  set Q : Polynomial ℝ := Polynomial.C (gchoose R T) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : Set.range ((Nat.cast : ℕ → ℝ))
        ⊆ {x | Polynomial.eval x P = Polynomial.eval x Q} := by
      intro x hx
      obtain ⟨Mn, rfl⟩ := hx
      simp only [Set.mem_ofPred_eq]
      have hsum : Polynomial.eval ((Mn : ℕ) : ℝ) P
          = ∑ k ∈ Finset.range (T + 1),
            abelB ((Mn : ℕ) : ℝ) (N : ℝ) k
              * gchoose (R - ((Mn : ℕ) : ℝ) - (N : ℝ) * (k : ℝ)) (T - k) := by
        rw [hP]
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
          BpolyM_eval, GpolyM_eval]
      have hQ : Polynomial.eval ((Mn : ℕ) : ℝ) Q = gchoose R T := by
        rw [hQdef]
        simp only [Polynomial.eval_C]
      rw [hsum, hQ]
      exact hagenRothe_nat N T R Mn
    have hinf : (Set.range ((Nat.cast : ℕ → ℝ))).Infinite :=
      Set.infinite_range_of_injective Nat.cast_injective
    exact Set.Infinite.mono hsub hinf
  have hPeval : Polynomial.eval M P
      = ∑ k ∈ Finset.range (T + 1),
        abelB M (N : ℝ) k * gchoose (R - M - (N : ℝ) * (k : ℝ)) (T - k) := by
    rw [hP]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      BpolyM_eval, GpolyM_eval]
  have hQeval : Polynomial.eval M Q = gchoose R T := by
    rw [hQdef]
    simp only [Polynomial.eval_C]
  have heval : Polynomial.eval M P = Polynomial.eval M Q := by
    rw [hPQ]
  rw [hPeval, hQeval] at heval
  exact heval

private noncomputable def BpolyN (M : ℝ) (k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.C M
      * (∏ i ∈ Finset.range j,
        (Polynomial.C (((j + 1 : ℕ)) : ℝ) * Polynomial.X
          + Polynomial.C (M - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

private lemma BpolyN_eval (M : ℝ) (k : ℕ) (N : ℝ) :
    Polynomial.eval N (BpolyN M k) = abelB M N k := by
  cases k with
  | zero =>
    simp only [BpolyN, abelB_zero, Polynomial.eval_one]
  | succ j =>
    simp only [BpolyN, abelB_succ, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C,
      div_eq_mul_inv]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring

private noncomputable def GpolyN (M : ℝ) (T : ℕ) (R : ℝ) (k : ℕ) :
    Polynomial ℝ :=
  (∏ i ∈ Finset.range (T - k),
    (Polynomial.C (R - M - (i : ℝ)) - Polynomial.X * Polynomial.C (k : ℝ)))
    * Polynomial.C (((Nat.factorial (T - k) : ℝ))⁻¹)

private lemma GpolyN_eval (M : ℝ) (T : ℕ) (R N : ℝ) (k : ℕ) :
    Polynomial.eval N (GpolyN M T R k)
      = gchoose (R - M - N * (k : ℝ)) (T - k) := by
  cases hTK : T - k with
  | zero =>
    simp only [GpolyN, hTK, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, inv_one, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_C, mul_one, gchoose_zero]
  | succ j =>
    have hg : gchoose (R - M - N * (k : ℝ)) (j + 1)
        = (∏ i ∈ Finset.range (j + 1), (R - M - N * (k : ℝ) - (i : ℝ)))
          / (Nat.factorial (j + 1) : ℝ) := by
      have h := gchoose_succ (R - M - N * (k : ℝ)) j
      exact h
    simp only [GpolyN]
    rw [hTK]
    simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv, hg]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring

private lemma hagenRothe_realMN (T : ℕ) (R M N : ℝ) :
    ∑ k ∈ Finset.range (T + 1),
        abelB M N k * gchoose (R - M - N * (k : ℝ)) (T - k)
      = gchoose R T := by
  set P : Polynomial ℝ :=
    ∑ k ∈ Finset.range (T + 1), BpolyN M k * GpolyN M T R k with hP
  set Q : Polynomial ℝ := Polynomial.C (gchoose R T) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : Set.range ((Nat.cast : ℕ → ℝ))
        ⊆ {x | Polynomial.eval x P = Polynomial.eval x Q} := by
      intro x hx
      obtain ⟨Nn, rfl⟩ := hx
      simp only [Set.mem_ofPred_eq]
      have hsum : Polynomial.eval ((Nn : ℕ) : ℝ) P
          = ∑ k ∈ Finset.range (T + 1),
            abelB M ((Nn : ℕ) : ℝ) k
              * gchoose (R - M - ((Nn : ℕ) : ℝ) * (k : ℝ)) (T - k) := by
        rw [hP]
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
          BpolyN_eval, GpolyN_eval]
      have hQ : Polynomial.eval ((Nn : ℕ) : ℝ) Q = gchoose R T := by
        rw [hQdef]
        simp only [Polynomial.eval_C]
      rw [hsum, hQ]
      exact hagenRothe_realM Nn T R M
    have hinf : (Set.range ((Nat.cast : ℕ → ℝ))).Infinite :=
      Set.infinite_range_of_injective Nat.cast_injective
    exact Set.Infinite.mono hsub hinf
  have hPeval : Polynomial.eval N P
      = ∑ k ∈ Finset.range (T + 1),
        abelB M N k * gchoose (R - M - N * (k : ℝ)) (T - k) := by
    rw [hP]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      BpolyN_eval, GpolyN_eval]
  have hQeval : Polynomial.eval N Q = gchoose R T := by
    rw [hQdef]
    simp only [Polynomial.eval_C]
  have heval : Polynomial.eval N P = Polynomial.eval N Q := by
    rw [hPQ]
  rw [hPeval, hQeval] at heval
  exact heval

private lemma expSeries_abelB_conv_nat (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (n : ℝ) (hn : 0 < n) (T : ℕ) :
    ∑ k ∈ Finset.range (T + 1),
        abelB (M : ℝ) n k * abelB (L : ℝ) n (T - k) =
      abelB ((M + L : ℕ) : ℝ) n T := by
  let R : ℝ := (M : ℝ) + (L : ℝ) + n * (T : ℝ)
  let G : ℝ := gchoose R T
  have hargM : ∀ k ∈ Finset.range (T + 1),
      R - (M : ℝ) - n * (k : ℝ) = (L : ℝ) + n * ((T - k : ℕ) : ℝ) := by
    intro k hk
    have hkT : k ≤ T := by
      have := Finset.mem_range.mp hk
      omega
    rw [Nat.cast_sub hkT]
    simp only [R]
    ring
  have hargL : ∀ k ∈ Finset.range (T + 1),
      R - (L : ℝ) - n * (((T - k : ℕ)) : ℝ) = (M : ℝ) + n * (k : ℝ) := by
    intro k hk
    have hkT : k ≤ T := by
      have := Finset.mem_range.mp hk
      omega
    rw [Nat.cast_sub hkT]
    simp only [R]
    ring
  have hleft : ∑ k ∈ Finset.range (T + 1),
        abelB (M : ℝ) n k *
          (((L : ℝ) + n * ((T - k : ℕ) : ℝ)) * abelB (L : ℝ) n (T - k))
      = (L : ℝ) * G := by
    have hHR := hagenRothe_realMN T R (M : ℝ) n
    simp only [G]
    rw [← hHR, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hargM k hk]
    have hb := expSeries_mul_abelB_eq_mul_gchoose (L : ℝ) n (T - k)
    rw [hb]
    ring
  have hright : ∑ k ∈ Finset.range (T + 1),
        (((M : ℝ) + n * (k : ℝ)) * abelB (M : ℝ) n k) *
          abelB (L : ℝ) n (T - k) = (M : ℝ) * G := by
    have hHR := hagenRothe_realMN T R (L : ℝ) n
    have href := Finset.sum_range_reflect
      (fun q => abelB (L : ℝ) n q *
        gchoose (R - (L : ℝ) - n * (q : ℝ)) (T - q)) (T + 1)
    have hrev : ∑ k ∈ Finset.range (T + 1),
          abelB (L : ℝ) n (T - k) *
            gchoose (R - (L : ℝ) - n * (((T - k : ℕ)) : ℝ)) k = G := by
      rw [show T + 1 - 1 = T by omega] at href
      calc
        _ = ∑ k ∈ Finset.range (T + 1),
              abelB (L : ℝ) n (T - k) *
                gchoose (R - (L : ℝ) - n * (((T - k : ℕ)) : ℝ))
                  (T - (T - k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkT : k ≤ T := by
              have := Finset.mem_range.mp hk
              omega
            have hsub : T - (T - k) = k := by omega
            rw [hsub]
        _ = ∑ k ∈ Finset.range (T + 1),
              abelB (L : ℝ) n k *
                gchoose (R - (L : ℝ) - n * (k : ℝ)) (T - k) := href
        _ = G := by simpa only [G] using hHR
    rw [← hrev, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hargL k hk]
    have hb := expSeries_mul_abelB_eq_mul_gchoose (M : ℝ) n k
    rw [hb]
    ring
  have hweighted : R * (∑ k ∈ Finset.range (T + 1),
        abelB (M : ℝ) n k * abelB (L : ℝ) n (T - k)) =
      ((M : ℝ) + (L : ℝ)) * G := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ k ∈ Finset.range (T + 1),
          (abelB (M : ℝ) n k *
              (((L : ℝ) + n * ((T - k : ℕ) : ℝ)) * abelB (L : ℝ) n (T - k)) +
            (((M : ℝ) + n * (k : ℝ)) * abelB (M : ℝ) n k) *
              abelB (L : ℝ) n (T - k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkT : k ≤ T := by
              have := Finset.mem_range.mp hk
              omega
            rw [Nat.cast_sub hkT]
            simp only [R]
            ring
      _ = (∑ k ∈ Finset.range (T + 1),
            abelB (M : ℝ) n k *
              (((L : ℝ) + n * ((T - k : ℕ) : ℝ)) * abelB (L : ℝ) n (T - k))) +
          ∑ k ∈ Finset.range (T + 1),
            (((M : ℝ) + n * (k : ℝ)) * abelB (M : ℝ) n k) *
              abelB (L : ℝ) n (T - k) := by rw [Finset.sum_add_distrib]
      _ = (L : ℝ) * G + (M : ℝ) * G := by rw [hleft, hright]
      _ = ((M : ℝ) + (L : ℝ)) * G := by ring
  have htotal := expSeries_mul_abelB_eq_mul_gchoose
    (((M + L : ℕ) : ℝ)) n T
  have hRpos : 0 < R := by
    simp only [R]
    have hMc : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hLc : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hT : 0 ≤ n * (T : ℝ) := mul_nonneg (le_of_lt hn) (Nat.cast_nonneg T)
    linarith
  have hcast : (((M + L : ℕ) : ℝ)) = (M : ℝ) + (L : ℝ) := by push_cast; ring
  rw [hcast] at htotal ⊢
  simp only [R, G] at hweighted
  nlinarith

private noncomputable def expSeries_Bpoly (n : ℝ) (k : ℕ) : Polynomial ℝ :=
  match k with
  | 0 => 1
  | j + 1 =>
    Polynomial.X * (∏ i ∈ Finset.range j,
      (Polynomial.X + Polynomial.C (((j + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ))))
      * Polynomial.C (((Nat.factorial (j + 1) : ℝ))⁻¹)

private lemma expSeries_Bpoly_eval (m n : ℝ) (k : ℕ) :
    Polynomial.eval m (expSeries_Bpoly n k) = abelB m n k := by
  cases k with
  | zero => simp [expSeries_Bpoly, abelB_zero]
  | succ j =>
    simp only [expSeries_Bpoly, abelB_succ, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C, div_eq_mul_inv]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring

private lemma expSeries_abelB_conv_of_posNat (m n : ℝ) (T : ℕ)
    (h : ∀ N : ℕ, 1 ≤ N →
      (∑ p ∈ Finset.antidiagonal T,
        abelB (N : ℝ) n p.1 * abelB m n p.2) = abelB ((N : ℝ) + m) n T)
    (t : ℝ) :
    (∑ p ∈ Finset.antidiagonal T, abelB t n p.1 * abelB m n p.2) =
      abelB (t + m) n T := by
  set P : Polynomial ℝ := ∑ p ∈ Finset.antidiagonal T,
    expSeries_Bpoly n p.1 * Polynomial.C (abelB m n p.2) with hP
  set Q : Polynomial ℝ := (expSeries_Bpoly n T).comp
    (Polynomial.X + Polynomial.C m) with hQ
  have hevalP : ∀ x : ℝ, Polynomial.eval x P =
      ∑ p ∈ Finset.antidiagonal T, abelB x n p.1 * abelB m n p.2 := by
    intro x
    rw [hP, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Polynomial.eval_mul, Polynomial.eval_C, expSeries_Bpoly_eval]
  have hevalQ : ∀ x : ℝ, Polynomial.eval x Q = abelB (x + m) n T := by
    intro x
    rw [hQ, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, expSeries_Bpoly_eval]
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun N : ℕ => (((N + 1 : ℕ)) : ℝ)) := by
      intro a b hab
      have : a + 1 = b + 1 := Nat.cast_injective hab
      omega
    have hmem : ∀ N : ℕ, (((N + 1 : ℕ)) : ℝ) ∈
        {x : ℝ | Polynomial.eval x P = Polynomial.eval x Q} := by
      intro N
      change Polynomial.eval (((N + 1 : ℕ)) : ℝ) P =
        Polynomial.eval (((N + 1 : ℕ)) : ℝ) Q
      rw [hevalP, hevalQ]
      exact h (N + 1) (by omega)
    exact Set.infinite_of_injective_forall_mem hinj hmem
  have hfin := congrArg (Polynomial.eval t) hPQ
  rw [hevalP, hevalQ] at hfin
  exact hfin

private lemma expSeries_abelB_conv (a b n : ℝ) (hn : 0 < n) (T : ℕ) :
    (∑ p ∈ Finset.antidiagonal T, abelB a n p.1 * abelB b n p.2) =
      abelB (a + b) n T := by
  have hnat : ∀ M L : ℕ, 1 ≤ M → 1 ≤ L →
      (∑ p ∈ Finset.antidiagonal T,
        abelB (M : ℝ) n p.1 * abelB (L : ℝ) n p.2) =
        abelB (((M + L : ℕ)) : ℝ) n T := by
    intro M L hM hL
    have hsum := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => abelB (M : ℝ) n i * abelB (L : ℝ) n j) T
    rw [hsum]
    simpa only [Nat.succ_eq_add_one] using expSeries_abelB_conv_nat M L hM hL n hn T
  have step1 : ∀ L : ℕ, 1 ≤ L → ∀ t : ℝ,
      (∑ p ∈ Finset.antidiagonal T,
        abelB t n p.1 * abelB (L : ℝ) n p.2) = abelB (t + (L : ℝ)) n T := by
    intro L hL t
    apply expSeries_abelB_conv_of_posNat (L : ℝ) n T _ t
    intro M hM
    have hML := hnat M L hM hL
    push_cast at hML
    exact hML
  have hswap : ∀ N : ℕ,
      (∑ p ∈ Finset.antidiagonal T, abelB (N : ℝ) n p.1 * abelB b n p.2) =
        ∑ p ∈ Finset.antidiagonal T, abelB b n p.1 * abelB (N : ℝ) n p.2 := by
    intro N
    have h := Finset.Nat.sum_antidiagonal_swap
      (f := fun p : ℕ × ℕ => abelB (N : ℝ) n p.1 * abelB b n p.2) (n := T)
    rw [← h]
    apply Finset.sum_congr rfl
    intro p _
    rcases p with ⟨i, j⟩
    simp only [Prod.swap_prod_mk]
    ring
  have step2 : ∀ N : ℕ, 1 ≤ N →
      (∑ p ∈ Finset.antidiagonal T, abelB (N : ℝ) n p.1 * abelB b n p.2) =
        abelB ((N : ℝ) + b) n T := by
    intro N hN
    rw [hswap N, add_comm]
    exact step1 N hN b
  exact expSeries_abelB_conv_of_posNat b n T step2 a

private lemma expSeries_abs_abelB_le_choose (m n : ℝ) (M k : ℕ)
    (hM : |m| ≤ (M : ℝ)) (hn : 1 < n) :
    |abelB m n k| ≤ ((M + ⌈n * (k : ℝ)⌉₊).choose k : ℕ) := by
  cases k with
  | zero => simp [abelB_zero]
  | succ j =>
    let N : ℕ := M + ⌈n * (((j + 1 : ℕ)) : ℝ)⌉₊
    have hjN : j + 1 ≤ N := by
      have hceil : (((j + 1 : ℕ)) : ℝ) <
          (⌈n * (((j + 1 : ℕ)) : ℝ)⌉₊ : ℝ) := by
        have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
        have hlt : (((j + 1 : ℕ)) : ℝ) < n * (((j + 1 : ℕ)) : ℝ) := by nlinarith
        exact lt_of_lt_of_le hlt (Nat.le_ceil _)
      have : j + 1 < ⌈n * (((j + 1 : ℕ)) : ℝ)⌉₊ := by exact_mod_cast hceil
      simp only [N]
      omega
    have hjceil : j + 1 ≤ ⌈n * (((j + 1 : ℕ)) : ℝ)⌉₊ := by
      have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      have hlt : (((j + 1 : ℕ)) : ℝ) < n * (((j + 1 : ℕ)) : ℝ) := by nlinarith
      have := lt_of_lt_of_le hlt (Nat.le_ceil (n * (((j + 1 : ℕ)) : ℝ)))
      exact_mod_cast (le_of_lt this)
    have hfactor : ∀ i ∈ Finset.range j,
        |m + (((j + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ)| ≤ ((N - i : ℕ) : ℝ) := by
      intro i hi
      have hij : i < j := Finset.mem_range.mp hi
      have hiN : i ≤ N := by omega
      have hijc : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      have hbase : 0 ≤ ((j : ℝ) + 1) * n - 1 - (i : ℝ) := by nlinarith
      have hceil : n * ((j : ℝ) + 1) ≤
          (⌈n * ((j : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
      rw [Nat.cast_sub hiN]
      simp only [N]
      push_cast
      change |m + ((j : ℝ) + 1) * n - 1 - (i : ℝ)| ≤
        (M : ℝ) + (⌈n * ((j : ℝ) + 1)⌉₊ : ℝ) - (i : ℝ)
      calc
        |m + ((j : ℝ) + 1) * n - 1 - (i : ℝ)|
            ≤ |m| + |((j : ℝ) + 1) * n - 1 - (i : ℝ)| := by
              have hadd := abs_add_le m (((j : ℝ) + 1) * n - 1 - (i : ℝ))
              ring_nf at hadd ⊢
              exact hadd
        _ = |m| + (((j : ℝ) + 1) * n - 1 - (i : ℝ)) := by
              rw [abs_of_nonneg hbase]
        _ ≤ (M : ℝ) + (⌈n * ((j : ℝ) + 1)⌉₊ : ℝ) - (i : ℝ) := by
              linarith
    have hprod : ∏ i ∈ Finset.range j,
          |m + (((j + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ)| ≤
        ∏ i ∈ Finset.range j, ((N - i : ℕ) : ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      exact hfactor
    have hlead : |m| ≤ ((N - j : ℕ) : ℝ) := by
      have hMN : M ≤ N - j := by
        simp only [N]
        omega
      exact hM.trans (by exact_mod_cast hMN)
    have hnum : |m| * ∏ i ∈ Finset.range j,
          |m + (((j + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ)| ≤
        ((N - j : ℕ) : ℝ) * ∏ i ∈ Finset.range j, ((N - i : ℕ) : ℝ) := by
      exact mul_le_mul hlead hprod (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        (Nat.cast_nonneg _)
    have hchoose : ((∏ i ∈ Finset.range (j + 1), (N - i)) : ℕ) /
          (Nat.factorial (j + 1) : ℝ) = (N.choose (j + 1) : ℕ) := by
      rw [← Nat.descFactorial_eq_prod_range, Nat.choose_eq_descFactorial_div_factorial]
      rw [Nat.cast_div (Nat.factorial_dvd_descFactorial N (j + 1))]
      exact_mod_cast Nat.factorial_ne_zero (j + 1)
    have hfacabs : |(Nat.factorial (j + 1) : ℝ)| = (Nat.factorial (j + 1) : ℝ) :=
      abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos (j + 1)))
    rw [abelB_succ, abs_div, abs_mul, Finset.abs_prod, hfacabs]
    calc
      |m| * (∏ i ∈ Finset.range j,
          |m + (((j + 1 : ℕ)) : ℝ) * n - 1 - (i : ℝ)|) /
            (Nat.factorial (j + 1) : ℝ)
          ≤ (((N - j : ℕ) : ℝ) * ∏ i ∈ Finset.range j, ((N - i : ℕ) : ℝ)) /
              (Nat.factorial (j + 1) : ℝ) :=
            div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
      _ = ((∏ i ∈ Finset.range (j + 1), (N - i)) : ℕ) /
            (Nat.factorial (j + 1) : ℝ) := by
              rw [Finset.prod_range_succ]
              push_cast
              ring
      _ = (N.choose (j + 1) : ℕ) := hchoose

private lemma expSeries_choose_probability_le_one (N k : ℕ) (p : ℝ)
    (hk : k ≤ N) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (N.choose k : ℕ) * p ^ k * (1 - p) ^ (N - k) ≤ 1 := by
  have hnonneg : ∀ i ∈ Finset.range (N + 1),
      0 ≤ p ^ i * (1 - p) ^ (N - i) * (N.choose i : ℕ) := by
    intro i _
    positivity
  have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum hnonneg hmem
  calc
    (N.choose k : ℕ) * p ^ k * (1 - p) ^ (N - k) =
        p ^ k * (1 - p) ^ (N - k) * (N.choose k : ℕ) := by ring
    _ ≤ ∑ i ∈ Finset.range (N + 1),
        p ^ i * (1 - p) ^ (N - i) * (N.choose i : ℕ) := hsingle
    _ = (p + (1 - p)) ^ N := (add_pow p (1 - p) N).symm
    _ = 1 := by ring

private lemma expSeries_entropy_pow_lt_one (n : ℝ) (hn1 : 1 < n) (hn2 : n < 2) :
    ((n / 2) ^ (1 / n) * (n / (2 * (n - 1))) ^ (1 - 1 / n)) ^ n < 1 := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hnm1 : 0 < n - 1 := sub_pos.mpr hn1
  have hp : 0 < 1 / n := one_div_pos.mpr hn0
  have hb : 0 < 1 - 1 / n := by
    rw [sub_pos, div_lt_one hn0]
    exact hn1
  have hweights : 1 / n + (1 - 1 / n) = 1 := by ring
  have hA : 0 ≤ n / 2 := by positivity
  have hB : 0 ≤ n / (2 * (n - 1)) := by positivity
  have hne : n / 2 ≠ n / (2 * (n - 1)) := by
    intro h
    field_simp at h
    nlinarith
  have hgm := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos
    hp hb hA hB hweights).2 hne
  have harith : (1 / n) * (n / 2) + (1 - 1 / n) * (n / (2 * (n - 1))) = 1 := by
    field_simp
    ring
  rw [harith] at hgm
  exact Real.rpow_lt_one (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    hgm hn0

private lemma expSeries_entropy_pow_eq (n : ℝ) (hn1 : 1 < n) :
    ((n / 2) ^ (1 / n) * (n / (2 * (n - 1))) ^ (1 - 1 / n)) ^ n =
      (n / 2) * (n / (2 * (n - 1))) ^ (n - 1) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (le_of_lt (by positivity : 0 < n / 2)) (1 / n) n,
    ← Real.rpow_mul (le_of_lt (by positivity : 0 < n / (2 * (n - 1))))
      (1 - 1 / n) n]
  have h1 : (1 / n) * n = 1 := by field_simp
  have h2 : (1 - 1 / n) * n = n - 1 := by field_simp
  rw [h1, h2, Real.rpow_one]

private lemma expSeries_entropy_base_lt_one (n : ℝ) (hn1 : 1 < n) (hn2 : n < 2) :
    (n / 2) * (n / (2 * (n - 1))) ^ (n - 1) < 1 := by
  rw [← expSeries_entropy_pow_eq n hn1]
  exact expSeries_entropy_pow_lt_one n hn1 hn2

private lemma expSeries_entropy_base_eq (n : ℝ) (hn1 : 1 < n) :
    (2 : ℝ) ^ (-n) / (1 / n) * (1 - 1 / n) ^ (-(n - 1)) =
      (n / 2) * (n / (2 * (n - 1))) ^ (n - 1) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hnm1 : 0 < n - 1 := sub_pos.mpr hn1
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hb : 0 < 1 - 1 / n := by
    rw [sub_pos, div_lt_one hn0]
    exact hn1
  have he1 : (2 : ℝ) ^ (-n) = (1 / 2) * (1 / 2) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ (-n) = (2 : ℝ) ^ ((-1 : ℝ) + (-(n - 1))) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ (-1 : ℝ) * (2 : ℝ) ^ (-(n - 1)) := Real.rpow_add h2 _ _
      _ = (1 / 2) * (1 / 2) ^ (n - 1) := by
        rw [Real.rpow_neg_one]
        have ht : (2 : ℝ) ^ (-(n - 1)) = (1 / 2) ^ (n - 1) := by
          calc
            (2 : ℝ) ^ (-(n - 1)) = ((2 : ℝ) ^ (n - 1))⁻¹ :=
              Real.rpow_neg h2.le (n - 1)
            _ = ((2 : ℝ)⁻¹) ^ (n - 1) := (Real.inv_rpow h2.le _).symm
            _ = (1 / 2) ^ (n - 1) := by norm_num
        rw [ht]
        norm_num
  have hbval : 1 - 1 / n = (n - 1) / n := by field_simp
  have he2 : ((n - 1) / n) ^ (-(n - 1)) = (n / (n - 1)) ^ (n - 1) := by
    calc
      ((n - 1) / n) ^ (-(n - 1)) = (((n - 1) / n) ^ (n - 1))⁻¹ :=
        Real.rpow_neg (by positivity) (n - 1)
      _ = (((n - 1) / n)⁻¹) ^ (n - 1) :=
        (Real.inv_rpow (by positivity) _).symm
      _ = (n / (n - 1)) ^ (n - 1) := by
        congr 1
        field_simp
  rw [he1, hbval, he2]
  have hcombine : (1 / 2) ^ (n - 1) * (n / (n - 1)) ^ (n - 1) =
      (n / (2 * (n - 1))) ^ (n - 1) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc
    (1 / 2) * (1 / 2) ^ (n - 1) / (1 / n) * (n / (n - 1)) ^ (n - 1) =
        (n / 2) * ((1 / 2) ^ (n - 1) * (n / (n - 1)) ^ (n - 1)) := by
          field_simp
    _ = (n / 2) * (n / (2 * (n - 1))) ^ (n - 1) := by rw [hcombine]

private lemma expSeries_probability_majorant (n p b z : ℝ) (M N k : ℕ)
    (hp : 0 < p) (hb : 0 < b) (hb1 : b ≤ 1) (hz : 0 ≤ z) (hkN : k ≤ N)
    (hN : (N - k : ℝ) ≤ (M : ℝ) + 1 + (n - 1) * (k : ℝ)) :
    (p ^ k * b ^ (N - k))⁻¹ * z ^ k ≤
      b ^ (-((M : ℝ) + 1)) * (z / p * b ^ (-(n - 1))) ^ k := by
  have hbrpow : b ^ (-((N - k : ℕ) : ℝ)) ≤
      b ^ (-((M : ℝ) + 1 + (n - 1) * (k : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_ge hb hb1
    rw [Nat.cast_sub hkN]
    linarith
  have hleft : (p ^ k * b ^ (N - k))⁻¹ * z ^ k =
      (z / p) ^ k * b ^ (-((N - k : ℕ) : ℝ)) := by
    rw [mul_inv, ← Real.rpow_natCast b (N - k), ← Real.rpow_neg hb.le]
    rw [← inv_pow]
    calc
      p⁻¹ ^ k * b ^ (-((N - k : ℕ) : ℝ)) * z ^ k =
          (p⁻¹ ^ k * z ^ k) * b ^ (-((N - k : ℕ) : ℝ)) := by ring
      _ = (p⁻¹ * z) ^ k * b ^ (-((N - k : ℕ) : ℝ)) := by rw [mul_pow]
      _ = (z / p) ^ k * b ^ (-((N - k : ℕ) : ℝ)) := by
        congr 2
        rw [div_eq_mul_inv]
        ring
  rw [hleft]
  calc
    (z / p) ^ k * b ^ (-((N - k : ℕ) : ℝ)) ≤
        (z / p) ^ k * b ^ (-((M : ℝ) + 1 + (n - 1) * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hbrpow (pow_nonneg (div_nonneg hz hp.le) k)
    _ = b ^ (-((M : ℝ) + 1)) * (z / p * b ^ (-(n - 1))) ^ k := by
      have he : -((M : ℝ) + 1 + (n - 1) * (k : ℝ)) =
          (-((M : ℝ) + 1)) + (-(n - 1)) * (k : ℝ) := by ring
      rw [he, Real.rpow_add hb, Real.rpow_mul hb.le,
        Real.rpow_natCast, mul_pow]
      ring

private lemma expSeries_summable_norm_high (m n x : ℝ)
    (hn1 : 1 < n) (hn2 : n < 2) (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    Summable (fun k : ℕ => ‖abelB m n k * x ^ k‖) := by
  let M : ℕ := ⌈|m|⌉₊
  let p : ℝ := 1 / n
  let b : ℝ := 1 - p
  let z : ℝ := (2 : ℝ) ^ (-n)
  let q : ℝ := z / p * b ^ (-(n - 1))
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hp : 0 < p := by simp only [p]; positivity
  have hp1 : p ≤ 1 := by
    simp only [p]
    rw [div_le_one hn0]
    exact hn1.le
  have hb : 0 < b := by
    simp only [b, p]
    rw [sub_pos, div_lt_one hn0]
    exact hn1
  have hb1 : b ≤ 1 := by simp only [b]; linarith
  have hz : 0 < z := by simp only [z]; positivity
  have hqeq : q = (n / 2) * (n / (2 * (n - 1))) ^ (n - 1) := by
    simp only [q, z, p, b]
    exact expSeries_entropy_base_eq n hn1
  have hq0 : 0 ≤ q := by simp only [q]; positivity
  have hq1 : q < 1 := by
    rw [hqeq]
    exact expSeries_entropy_base_lt_one n hn1 hn2
  have hmajor : Summable
      (fun k : ℕ => b ^ (-((M : ℝ) + 1)) * q ^ k) := by
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hterms : Summable (fun k : ℕ => abelB m n k * x ^ k) := by
    apply hmajor.of_norm_bounded
    intro k
    let N : ℕ := M + ⌈n * (k : ℝ)⌉₊
    have hkceil : k ≤ ⌈n * (k : ℝ)⌉₊ := by
      have hkreal : (k : ℝ) ≤ n * (k : ℝ) := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
      have hcast : (k : ℝ) ≤ (⌈n * (k : ℝ)⌉₊ : ℝ) :=
        hkreal.trans (Nat.le_ceil _)
      exact_mod_cast hcast
    have hkN : k ≤ N := by simp only [N]; omega
    have hN : (N - k : ℝ) ≤ (M : ℝ) + 1 + (n - 1) * (k : ℝ) := by
      simp only [N]
      push_cast
      have hceil := Nat.ceil_lt_add_one
        (mul_nonneg hn0.le (Nat.cast_nonneg k) : 0 ≤ n * (k : ℝ))
      linarith
    have hM : |m| ≤ (M : ℝ) := by simp only [M]; exact Nat.le_ceil _
    have hab : |abelB m n k| ≤ (N.choose k : ℕ) := by
      simpa only [N] using expSeries_abs_abelB_le_choose m n M k hM hn1
    have hprob := expSeries_choose_probability_le_one N k p hkN hp.le hp1
    have hweight : 0 < p ^ k * b ^ (N - k) := by positivity
    have hchoose : (N.choose k : ℝ) ≤ (p ^ k * b ^ (N - k))⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hweight]
      nlinarith [hprob]
    have hxpow : |x| ^ k ≤ z ^ k :=
      pow_le_pow_left₀ (abs_nonneg x) (hx.trans_eq rfl) k
    rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
    calc
      |abelB m n k| * |x| ^ k ≤ (N.choose k : ℝ) * |x| ^ k :=
        mul_le_mul_of_nonneg_right hab (pow_nonneg (abs_nonneg x) k)
      _ ≤ (N.choose k : ℝ) * z ^ k :=
        mul_le_mul_of_nonneg_left hxpow (Nat.cast_nonneg _)
      _ ≤ (p ^ k * b ^ (N - k))⁻¹ * z ^ k :=
        mul_le_mul_of_nonneg_right hchoose (pow_nonneg hz.le k)
      _ ≤ b ^ (-((M : ℝ) + 1)) * (z / p * b ^ (-(n - 1))) ^ k :=
        expSeries_probability_majorant n p b z M N k hp hb hb1 hz.le hkN hN
      _ = b ^ (-((M : ℝ) + 1)) * q ^ k := rfl
  exact hterms.norm

private lemma expSeries_summable_norm (m n x : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1)
    (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    Summable (fun k : ℕ => ‖abelB m n k * x ^ k‖) := by
  rcases lt_or_gt_of_ne hn_ne with hn1 | hn1
  · apply expSeries_summable_norm_low m n x hn0 hn1
    have hz1 : (2 : ℝ) ^ (-n) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hn0)
    exact hx.trans_lt hz1
  · exact expSeries_summable_norm_high m n x hn1 hn2 hx

private noncomputable def expSeries_F (m n x : ℝ) : ℝ :=
  ∑' k : ℕ, abelB m n k * x ^ k

private lemma expSeries_antidiagonal_pow (f g : ℕ → ℝ) (x : ℝ) (k : ℕ) :
    (∑ p ∈ Finset.antidiagonal k, (f p.1 * x ^ p.1) * (g p.2 * x ^ p.2)) =
      (∑ p ∈ Finset.antidiagonal k, f p.1 * g p.2) * x ^ k := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpm := Finset.mem_antidiagonal.mp hp
  have hxp : x ^ p.1 * x ^ p.2 = x ^ k := by rw [← pow_add, hpm]
  calc
    (f p.1 * x ^ p.1) * (g p.2 * x ^ p.2) =
        (f p.1 * g p.2) * (x ^ p.1 * x ^ p.2) := by ring
    _ = (f p.1 * g p.2) * x ^ k := by rw [hxp]

private lemma expSeries_tsum_mul_tsum (f g : ℕ → ℝ) (x : ℝ)
    (hf : Summable (fun k => ‖f k * x ^ k‖))
    (hg : Summable (fun k => ‖g k * x ^ k‖)) :
    (∑' k, f k * x ^ k) * (∑' k, g k * x ^ k) =
      ∑' k, (∑ p ∈ Finset.antidiagonal k, f p.1 * g p.2) * x ^ k := by
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun k => f k * x ^ k) (g := fun k => g k * x ^ k) hf hg
  simp only [expSeries_antidiagonal_pow] at h
  exact h

private lemma expSeries_F_mul (a b n x : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1)
    (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    expSeries_F a n x * expSeries_F b n x = expSeries_F (a + b) n x := by
  simp only [expSeries_F]
  rw [expSeries_tsum_mul_tsum _ _ _
    (expSeries_summable_norm a n x hn0 hn2 hn_ne hx)
    (expSeries_summable_norm b n x hn0 hn2 hn_ne hx)]
  apply tsum_congr
  intro k
  rw [expSeries_abelB_conv a b n hn0]

private lemma expSeries_F_zero (n x : ℝ) : expSeries_F 0 n x = 1 := by
  have hzero : ∀ k : ℕ, k ≠ 0 → abelB 0 n k * x ^ k = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [abelB_zero_succ, zero_mul]
  simp only [expSeries_F]
  rw [tsum_eq_single 0 hzero]
  simp [abelB_zero]

private lemma expSeries_F_pos (m n x : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1)
    (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    0 < expSeries_F m n x := by
  have hsq : expSeries_F m n x = (expSeries_F (m / 2) n x) ^ 2 := by
    have h := expSeries_F_mul (m / 2) (m / 2) n x hn0 hn2 hn_ne hx
    have he : m / 2 + m / 2 = m := by ring
    rw [he] at h
    rw [sq]
    exact h.symm
  have hnonneg : 0 ≤ expSeries_F m n x := by
    rw [hsq]
    exact sq_nonneg _
  have hne : expSeries_F m n x ≠ 0 := by
    have h := expSeries_F_mul m (-m) n x hn0 hn2 hn_ne hx
    rw [add_neg_cancel, expSeries_F_zero] at h
    intro hz
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private lemma expSeries_measurable_F (n x : ℝ) :
    Measurable (fun m : ℝ => expSeries_F m n x) := by
  simp only [expSeries_F]
  apply Measurable.tsum
  intro k
  have hfun : (fun m : ℝ => abelB m n k * x ^ k) =
      fun m : ℝ => Polynomial.eval m (expSeries_Bpoly n k) * x ^ k := by
    funext m
    rw [expSeries_Bpoly_eval]
  rw [hfun]
  exact ((expSeries_Bpoly n k).continuous.mul_const _).measurable

private lemma expSeries_F_eq_rpow (m n x : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1)
    (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    expSeries_F m n x = (expSeries_F 1 n x) ^ m := by
  have hpos : ∀ t : ℝ, 0 < expSeries_F t n x :=
    fun t => expSeries_F_pos t n x hn0 hn2 hn_ne hx
  have hne : ∀ t : ℝ, expSeries_F t n x ≠ 0 := fun t => ne_of_gt (hpos t)
  have hadd : ∀ a b : ℝ,
      expSeries_F (a + b) n x = expSeries_F a n x * expSeries_F b n x :=
    fun a b => (expSeries_F_mul a b n x hn0 hn2 hn_ne hx).symm
  have hlog_add : ∀ a b : ℝ,
      Real.log (expSeries_F (a + b) n x) =
        Real.log (expSeries_F a n x) + Real.log (expSeries_F b n x) := by
    intro a b
    rw [hadd, Real.log_mul (hne a) (hne b)]
  let L : ℝ →+ ℝ := AddMonoidHom.mk' (fun t => Real.log (expSeries_F t n x)) hlog_add
  have hLmeas : Measurable L := by
    change Measurable (fun t : ℝ => Real.log (expSeries_F t n x))
    exact (expSeries_measurable_F n x).log
  have hLcont : Continuous L :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable L hLmeas
  have hsmul : Real.log (expSeries_F m n x) =
      m • Real.log (expSeries_F 1 n x) := by
    have h := map_real_smul L hLcont m 1
    simpa [L] using h
  have hF1 : 0 < expSeries_F 1 n x := hpos 1
  calc
    expSeries_F m n x = Real.exp (Real.log (expSeries_F m n x)) :=
      (Real.exp_log (hpos m)).symm
    _ = Real.exp (m • Real.log (expSeries_F 1 n x)) := by rw [hsmul]
    _ = Real.exp (Real.log (expSeries_F 1 n x) * m) := by rw [smul_eq_mul, mul_comm]
    _ = (expSeries_F 1 n x) ^ m := by rw [Real.rpow_def_of_pos hF1]

private lemma expSeries_abelB_one_succ (n : ℝ) (k : ℕ) :
    abelB 1 n (k + 1) = abelB n n k := by
  have h := abelB_rec 1 n k
  simpa [abelB_zero_succ] using h

private lemma expSeries_F_one_equation (n x : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1)
    (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    expSeries_F 1 n x = 1 + x * expSeries_F n n x := by
  have hsum1 := (expSeries_summable_norm 1 n x hn0 hn2 hn_ne hx).of_norm
  have hsumn := (expSeries_summable_norm n n x hn0 hn2 hn_ne hx).of_norm
  have hsplit := hsum1.tsum_eq_zero_add
  simp only [abelB_zero, pow_zero, mul_one] at hsplit
  simp only [expSeries_F]
  rw [hsplit]
  congr 1
  rw [← hsumn.tsum_mul_left x]
  apply tsum_congr
  intro k
  rw [expSeries_abelB_one_succ, pow_succ]
  ring

private lemma expSeries_F_one_root_equation (n x : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1)
    (hx : |x| ≤ (2 : ℝ) ^ (-n)) :
    expSeries_F 1 n x = 1 + x * (expSeries_F 1 n x) ^ n := by
  calc
    expSeries_F 1 n x = 1 + x * expSeries_F n n x :=
      expSeries_F_one_equation n x hn0 hn2 hn_ne hx
    _ = 1 + x * (expSeries_F 1 n x) ^ n := by
      rw [expSeries_F_eq_rpow n n x hn0 hn2 hn_ne hx]

private noncomputable def expSeries_phi (n y : ℝ) : ℝ :=
  (y - 1) / y ^ n

private lemma expSeries_phi_eq_of_root (n z y : ℝ) (hy0 : 0 < y)
    (hroot : y = 1 + z * y ^ n) :
    expSeries_phi n y = z := by
  simp only [expSeries_phi]
  apply (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hy0 _))).2
  linarith

private lemma expSeries_phi_two (n : ℝ) :
    expSeries_phi n 2 = (2 : ℝ) ^ (-n) := by
  simp only [expSeries_phi]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma expSeries_phi_strictMonoOn (n c : ℝ)
    (hlin : ∀ y ∈ Set.Ioo (1 : ℝ) c, 0 < n + (1 - n) * y) :
    StrictMonoOn (expSeries_phi n) (Set.Icc 1 c) := by
  have hcont : ContinuousOn (expSeries_phi n) (Set.Icc 1 c) := by
    have hpow : ContinuousOn (fun y : ℝ => y ^ n) (Set.Icc 1 c) :=
      continuousOn_id.rpow_const fun y hy =>
        Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hy.1))
    exact (continuousOn_id.sub continuousOn_const).div hpow fun y hy =>
      ne_of_gt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hy.1) _)
  apply strictMonoOn_of_deriv_pos (convex_Icc 1 c) hcont
  intro y hy
  rw [interior_Icc] at hy
  have hy0 : 0 < y := lt_trans zero_lt_one hy.1
  have hden : HasDerivAt (fun t : ℝ => t ^ n) (n * y ^ (n - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy0.ne')
  have hderiv : HasDerivAt (expSeries_phi n)
      ((1 * y ^ n - (y - 1) * (n * y ^ (n - 1))) / (y ^ n) ^ 2) y := by
    exact ((hasDerivAt_id y).sub_const 1).div hden
      (ne_of_gt (Real.rpow_pos_of_pos hy0 _))
  rw [hderiv.deriv]
  have hpow : y ^ n = y ^ (n - 1) * y := by
    calc
      y ^ n = y ^ ((n - 1) + 1) := by congr 1; ring
      _ = y ^ (n - 1) * y ^ (1 : ℝ) := by rw [Real.rpow_add hy0]
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  have hnum :
      1 * (y ^ (n - 1) * y) - (y - 1) * (n * y ^ (n - 1)) =
        y ^ (n - 1) * (n + (1 - n) * y) := by
    ring
  rw [hnum]
  have hliny := hlin y hy
  positivity

private lemma expSeries_continuousOn_F_one (n : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1) :
    ContinuousOn (fun x => expSeries_F 1 n x) (Set.Icc 0 ((2 : ℝ) ^ (-n))) := by
  have hz0 : 0 < (2 : ℝ) ^ (-n) := Real.rpow_pos_of_pos (by norm_num) _
  have hmajor := expSeries_summable_norm 1 n ((2 : ℝ) ^ (-n)) hn0 hn2 hn_ne
    (by rw [abs_of_pos hz0])
  simp only [expSeries_F]
  apply continuousOn_tsum
    (fun k => (continuous_const.mul (continuous_id.pow k)).continuousOn) hmajor
  intro k x hx
  have hxabs : |x| ≤ (2 : ℝ) ^ (-n) := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  change ‖abelB 1 n k * x ^ k‖ ≤
    ‖abelB 1 n k * ((2 : ℝ) ^ (-n)) ^ k‖
  simp only [norm_mul, Real.norm_eq_abs, norm_pow, abs_of_pos hz0]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg x) hxabs k) (abs_nonneg _)

private lemma expSeries_F_at_zero (m n : ℝ) :
    expSeries_F m n 0 = 1 := by
  simp only [expSeries_F]
  rw [tsum_eq_single 0]
  · simp [abelB_zero]
  · intro k hk
    simp [zero_pow hk]

private lemma expSeries_endpoint_lt_critical (n : ℝ) (hn1 : 1 < n) (hn2 : n < 2) :
    (2 : ℝ) ^ (-n) < (1 / n) * (1 - 1 / n) ^ (n - 1) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hb : 0 < 1 - 1 / n := by
    rw [sub_pos, div_lt_one hn0]
    exact hn1
  have hq : (2 : ℝ) ^ (-n) / (1 / n) * (1 - 1 / n) ^ (-(n - 1)) < 1 := by
    rw [expSeries_entropy_base_eq n hn1]
    exact expSeries_entropy_base_lt_one n hn1 hn2
  let crit : ℝ := (1 / n) * (1 - 1 / n) ^ (n - 1)
  have hcrit : 0 < crit := by
    simp only [crit]
    positivity
  have hmul :
      ((2 : ℝ) ^ (-n) / (1 / n) * (1 - 1 / n) ^ (-(n - 1))) * crit =
        (2 : ℝ) ^ (-n) := by
    simp only [crit]
    rw [Real.rpow_neg hb.le (n - 1)]
    field_simp
  have h := mul_lt_mul_of_pos_right hq hcrit
  rw [hmul, one_mul] at h
  exact h

private lemma expSeries_critical_fixed_point (n : ℝ) (hn1 : 1 < n) :
    1 + ((1 / n) * (1 - 1 / n) ^ (n - 1)) * (n / (n - 1)) ^ n =
      n / (n - 1) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hnm1 : 0 < n - 1 := sub_pos.mpr hn1
  have hbval : 1 - 1 / n = (n - 1) / n := by
    field_simp
  rw [hbval]
  have hcval : n / (n - 1) = (((n - 1) / n)⁻¹) := by
    field_simp
  rw [hcval, Real.inv_rpow (by positivity)]
  have hpow : ((n - 1) / n) ^ n =
      ((n - 1) / n) ^ (n - 1) * ((n - 1) / n) := by
    calc
      _ = ((n - 1) / n) ^ ((n - 1) + 1) := by congr 1; ring
      _ = ((n - 1) / n) ^ (n - 1) * ((n - 1) / n) ^ (1 : ℝ) := by
        rw [Real.rpow_add (by positivity)]
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  have hA : ((n - 1) / n) ^ (n - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  field_simp
  ring

private lemma expSeries_F_one_lt_critical (n : ℝ) (hn1 : 1 < n) (hn2 : n < 2) :
    expSeries_F 1 n ((2 : ℝ) ^ (-n)) < n / (n - 1) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn1
  have hn_ne : n ≠ 1 := ne_of_gt hn1
  have hnm1 : 0 < n - 1 := sub_pos.mpr hn1
  have hz0 : 0 < (2 : ℝ) ^ (-n) := Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : 1 < n / (n - 1) := by
    rw [lt_div_iff₀ hnm1]
    linarith
  by_contra hnot
  have hcle : n / (n - 1) ≤ expSeries_F 1 n ((2 : ℝ) ^ (-n)) := le_of_not_gt hnot
  have hcont := expSeries_continuousOn_F_one n hn0 hn2 hn_ne
  have hIV := intermediate_value_Icc hz0.le hcont
  have hcmem : n / (n - 1) ∈ Set.Icc (expSeries_F 1 n 0)
      (expSeries_F 1 n ((2 : ℝ) ^ (-n))) := by
    rw [expSeries_F_at_zero]
    exact ⟨hc1.le, hcle⟩
  obtain ⟨t, ht, hteq⟩ := hIV hcmem
  have htabs : |t| ≤ (2 : ℝ) ^ (-n) := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hroot := expSeries_F_one_root_equation n t hn0 hn2 hn_ne htabs
  change expSeries_F 1 n t = n / (n - 1) at hteq
  rw [hteq] at hroot
  have htcrit : t < (1 / n) * (1 - 1 / n) ^ (n - 1) :=
    ht.2.trans_lt (expSeries_endpoint_lt_critical n hn1 hn2)
  have hcpow : 0 < (n / (n - 1)) ^ n :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hc1) _
  have hlt :
      1 + t * (n / (n - 1)) ^ n <
        1 + ((1 / n) * (1 - 1 / n) ^ (n - 1)) * (n / (n - 1)) ^ n :=
    by
      simpa [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right htcrit hcpow) 1
  rw [expSeries_critical_fixed_point n hn1, ← hroot] at hlt
  exact (lt_irrefl _ hlt)

private lemma expSeries_F_one_endpoint (n : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1) :
    expSeries_F 1 n ((2 : ℝ) ^ (-n)) = 2 := by
  have hz0 : 0 < (2 : ℝ) ^ (-n) := Real.rpow_pos_of_pos (by norm_num) _
  have hzabs : |(2 : ℝ) ^ (-n)| ≤ (2 : ℝ) ^ (-n) := by
    rw [abs_of_pos hz0]
  have hy0 : 0 < expSeries_F 1 n ((2 : ℝ) ^ (-n)) :=
    expSeries_F_pos 1 n _ hn0 hn2 hn_ne hzabs
  have hroot := expSeries_F_one_root_equation n ((2 : ℝ) ^ (-n))
    hn0 hn2 hn_ne hzabs
  have hy1 : 1 ≤ expSeries_F 1 n ((2 : ℝ) ^ (-n)) := by
    rw [hroot]
    exact le_add_of_nonneg_right (mul_nonneg hz0.le (Real.rpow_nonneg hy0.le _))
  have hphi : expSeries_phi n (expSeries_F 1 n ((2 : ℝ) ^ (-n))) =
      (2 : ℝ) ^ (-n) :=
    expSeries_phi_eq_of_root n _ _ hy0 hroot
  have hphi_two := expSeries_phi_two n
  rcases lt_or_gt_of_ne hn_ne with hn1 | hn1
  · let c := max (expSeries_F 1 n ((2 : ℝ) ^ (-n))) 2
    have hmono : StrictMonoOn (expSeries_phi n) (Set.Icc 1 c) := by
      apply expSeries_phi_strictMonoOn
      intro y hy
      have hcoef : 0 < 1 - n := sub_pos.mpr hn1
      have hypos : 0 < y := lt_trans zero_lt_one hy.1
      have hprod : 0 < (1 - n) * y := mul_pos hcoef hypos
      linarith
    apply hmono.injOn
    · exact ⟨hy1, le_max_left _ _⟩
    · exact ⟨by norm_num, le_max_right _ _⟩
    · exact hphi.trans hphi_two.symm
  · have hnm1 : 0 < n - 1 := sub_pos.mpr hn1
    have h2c : 2 < n / (n - 1) := by
      rw [lt_div_iff₀ hnm1]
      nlinarith
    have hmono : StrictMonoOn (expSeries_phi n) (Set.Icc 1 (n / (n - 1))) := by
      apply expSeries_phi_strictMonoOn
      intro y hy
      have hbound : y * (n - 1) < n := (lt_div_iff₀ hnm1).mp hy.2
      nlinarith
    apply hmono.injOn
    · exact ⟨hy1, (expSeries_F_one_lt_critical n hn1 hn2).le⟩
    · exact ⟨by norm_num, h2c.le⟩
    · exact hphi.trans hphi_two.symm

private lemma expSeries_hasSum_endpoint (m n : ℝ)
    (hn0 : 0 < n) (hn2 : n < 2) (hn_ne : n ≠ 1) :
    HasSum (fun k : ℕ => abelB m n k * (((2 : ℝ) ^ (-n)) ^ k)) ((2 : ℝ) ^ m) := by
  have hz0 : 0 < (2 : ℝ) ^ (-n) := Real.rpow_pos_of_pos (by norm_num) _
  have hzabs : |(2 : ℝ) ^ (-n)| ≤ (2 : ℝ) ^ (-n) := by
    rw [abs_of_pos hz0]
  have hsum := (expSeries_summable_norm m n ((2 : ℝ) ^ (-n))
    hn0 hn2 hn_ne hzabs).of_norm.hasSum
  change HasSum (fun k : ℕ => abelB m n k * (((2 : ℝ) ^ (-n)) ^ k))
    (expSeries_F m n ((2 : ℝ) ^ (-n))) at hsum
  rw [expSeries_F_eq_rpow m n _ hn0 hn2 hn_ne hzabs,
    expSeries_F_one_endpoint n hn0 hn2 hn_ne] at hsum
  exact hsum

private lemma expSeries_prod_two_eq_Ico (m : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    (∏ i ∈ Finset.range (k - 1), (m + (k : ℝ) * 2 - 1 - (i : ℝ))) =
      ∏ j ∈ Finset.Ico (k + 1) (2 * k), (m + (j : ℝ)) := by
  rw [Finset.prod_Ico_eq_prod_range]
  have hlen : 2 * k - (k + 1) = k - 1 := by omega
  rw [hlen]
  rw [← Finset.prod_range_reflect
    (fun i : ℕ => m + ((k + 1 + i : ℕ) : ℝ)) (k - 1)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hid : k + 1 + (k - 1 - 1 - i) = 2 * k - 1 - i := by omega
  rw [hid]
  have hii : i ≤ 2 * k - 1 := by omega
  have hk1 : 1 ≤ 2 * k := by omega
  rw [Nat.cast_sub hii, Nat.cast_sub hk1]
  push_cast
  ring

private lemma expSeries_abelB_two_tail (m : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    abelB m 2 k * (1 / 4 : ℝ) ^ k =
      m * ((∏ j ∈ Finset.Ico (k + 1) (2 * k), (m + (j : ℝ))) *
        (1 / 4 : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hprod := expSeries_prod_two_eq_Ico m (j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hprod
  rw [abelB_succ, hprod]
  ring

private lemma expSeries_hasSum_endpoint_two (m : ℝ) :
    HasSum (fun k : ℕ => abelB m 2 k * (1 / 4 : ℝ) ^ k) ((2 : ℝ) ^ m) := by
  let term : ℕ → ℝ := fun k => if k < 2 then 0 else
    (∏ j ∈ Finset.Ico (k + 1) (2 * k), (m + (j : ℝ))) *
      (1 / 4 : ℝ) ^ k / (Nat.factorial k : ℝ)
  have hcat :=
    Entry14Cor1Catalanpowerseries.ramanujan_part1_ch3_entry14_cor1_catalanpowerseries
      m (1 / 4) (by norm_num)
  change Summable term ∧
    Real.rpow (2 / (1 + Real.sqrt (1 - 4 * (1 / 4)))) m =
      1 + m * (1 / 4) + m * ∑' k, term k at hcat
  have hvalue := hcat.2.symm
  norm_num at hvalue
  have hzero : HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have hone : HasSum (fun k : ℕ => if k = 1 then m * (1 / 4) else 0)
      (m * (1 / 4)) := hasSum_ite_eq 1 _
  have htail : HasSum (fun k => m * term k) (m * ∑' k, term k) :=
    hcat.1.hasSum.mul_left m
  have hsum := (hzero.add hone).add htail
  rw [hvalue] at hsum
  apply HasSum.congr_fun hsum
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [abelB_zero, term]
  by_cases hk1 : k = 1
  · subst k
    simp [abelB_one, term]
  have hk2 : 2 ≤ k := by omega
  have hknot : ¬ k ≤ 1 := by omega
  simpa [hk0, hk1, term, hknot] using expSeries_abelB_two_tail m k hk2

private lemma series_term_eq (m n : ℝ) (k : ℕ) :
    (if k = 0 then (1 : ℝ)
      else (m * ∏ j ∈ Finset.range (k - 1), (m + (k : ℝ) * n - ((j : ℝ) + 1))) /
        ((2 : ℝ) ^ ((k : ℝ) * n) * (Nat.factorial k : ℝ)))
    = abelB m n k * (((2 : ℝ) ^ (-n)) ^ k) := by
  cases k with
  | zero =>
    simp only [abelB_zero, pow_zero, mul_one, ite_true]
  | succ j =>
    have hsub : j + 1 - 1 = j := by
      omega
    have hprod : ∏ t ∈ Finset.range (j + 1 - 1),
          (m + ((j + 1 : ℕ) : ℝ) * n - ((t : ℝ) + 1))
        = ∏ i ∈ Finset.range j, (m + ((j + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ)) := by
      rw [hsub]
      apply Finset.prod_congr rfl
      intro i _
      ring
    have hne : (j + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero j
    rw [ite_eq_right hne]
    have h2pos : (0 : ℝ) ≤ 2 := by
      norm_num
    have hrpow : (((2 : ℝ) ^ (-n)) ^ (j + 1 : ℕ))
        = (((2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * n))⁻¹) := by
      have e1 : (((2 : ℝ) ^ (-n)) ^ (j + 1 : ℕ))
          = (2 : ℝ) ^ ((-n) * ((j + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h2pos]
      have e2 : ((-n) * ((j + 1 : ℕ) : ℝ)) = -(((j + 1 : ℕ) : ℝ) * n) := by
        ring
      have e3 : (2 : ℝ) ^ (-(((j + 1 : ℕ) : ℝ) * n))
          = (((2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * n))⁻¹) := by
        rw [Real.rpow_neg h2pos]
      rw [e1, e2, e3]
    have hab : abelB m n (j + 1)
        = (m * ∏ i ∈ Finset.range j, (m + ((j + 1 : ℕ) : ℝ) * n - 1 - (i : ℝ)))
          / (Nat.factorial (j + 1) : ℝ) :=
      abelB_succ m n j
    rw [hab, hprod, mul_comm ((2 : ℝ) ^ _) _, div_mul_eq_div_div,
      div_eq_mul_inv, hrpow, mul_comm]

/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 15, Example 1, printed pp.
    73-75 / PDF pp. 83-85.

Proves `Wanted` entry `ramanujan_part1_ch3_entry15_example1_exponential_series`.

Proof: Following Berndt and the generalized binomial series of Graham, Knuth, and Patashnik,
the series is realized as `B_n(z) ^ m` with `B_n = 1 + z * B_n ^ n`; root selection at
`z = 2 ^ (-n)`, with the endpoint supplied by Entry 14's Catalan-power series, gives `B_n = 2`.
-/
theorem ramanujan_part1_ch3_entry15_example1_exponential_series (m n : ℝ)
    (hn_pos : 0 < n) (hn_le : n ≤ 2) :
    HasSum (fun k : ℕ =>
      if k = 0 then (1 : ℝ)
      else (m * ∏ j ∈ Finset.range (k - 1), (m + (k : ℝ) * n - ((j : ℝ) + 1))) /
        ((2 : ℝ) ^ ((k : ℝ) * n) * (Nat.factorial k : ℝ))) ((2 : ℝ) ^ m) := by
  by_cases hm : m = 0
  · subst hm
    exact expSeries_hasSum_m_zero n
  · by_cases hn_two : n = 2
    · subst n
      apply HasSum.congr_fun (expSeries_hasSum_endpoint_two m)
      intro k
      rw [series_term_eq]
      norm_num
    by_cases hn_one : n = 1
    · subst n
      apply HasSum.congr_fun (expSeries_hasSum_abelB_n_one m)
      intro k
      rw [series_term_eq]
      norm_num
    have hn_lt : n < 2 := lt_of_le_of_ne hn_le hn_two
    apply HasSum.congr_fun (expSeries_hasSum_endpoint m n hn_pos hn_lt hn_one)
    intro k
    exact series_term_eq m n k

end Entry15Example1ExponentialSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
