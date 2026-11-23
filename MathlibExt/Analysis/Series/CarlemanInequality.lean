/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Carleman's inequality (sharp form, constant `e`)

For a nonnegative sequence `a`, let `G n` be the geometric mean of the first
`n + 1` terms. Carleman's inequality says that

  `∑' n, G n ≤ Real.exp 1 * ∑' n, a n`,

with the sharp constant `e`. The proof is Knopp's induction: the strengthened
finite bound

  `(∑ n in Finset.range (M + 1), G n) + (M + 1) * G M ≤ e * ∑ n in Finset.range (M + 1), a n`

is proved by induction on `M`, where the induction step is the one-variable
inequality `(n + 2) * (x ^ n * y) ^ (1 / (n + 1)) ≤ n * x + e * y`, itself a
consequence of Young's inequality with the bound
`((n + 2) / (n + 1)) ^ (n + 1) = (1 + 1 / (n + 1)) ^ (n + 1) < e`.

This is the sharp quantitative form: the companion file
`MathlibExt/MeasureTheory/Integral/CarlemanStieltjesCriterion.lean` proves only
summability of the geometric means (`summable_geometric_means`), not the bound
with constant `e`, and its proof in fact only gives the constant `2 * e`.

Source: T. Carleman, *Sur les fonctions quasi-analytiques* (1923); see also
Hardy–Littlewood–Pólya, *Inequalities*, Theorem 337. Companion to the
Hölder / Minkowski / `Lᵖ` material of
`v1/Atlas/IntroductionToFunctionalAnalysis` (not one of the 72 numbered targets).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The geometric mean of the first `n + 1` terms of a sequence `a`. -/
noncomputable def carlemanGeomMean (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range (n + 1), a k) ^ ((((n + 1 : ℕ) : ℝ))⁻¹)

theorem carlemanGeomMean_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ carlemanGeomMean a n := by
  unfold carlemanGeomMean
  exact Real.rpow_nonneg (Finset.prod_nonneg fun i _ => ha i) _

private lemma carlemanGeomMean_zero (a : ℕ → ℝ) : carlemanGeomMean a 0 = a 0 := by
  simp [carlemanGeomMean]

private lemma carlemanGeomMean_succ {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    carlemanGeomMean a (n + 1) =
      ((carlemanGeomMean a n) ^ (n + 1) * a (n + 1)) ^ ((((n + 1) + 1 : ℕ) : ℝ))⁻¹ := by
  unfold carlemanGeomMean
  rw [Finset.prod_range_succ,
    Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => ha i) (by omega : n + 1 ≠ 0)]

private lemma one_add_div_pow_lt_exp {m : ℕ} (hm : 1 ≤ m) :
    ((1 : ℝ) + 1 / (m : ℝ)) ^ m < Real.exp 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbase : (0 : ℝ) < (1 : ℝ) + 1 / (m : ℝ) := by positivity
  have hne : (1 : ℝ) + 1 / (m : ℝ) ≠ 1 := by
    have h1m : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    intro h
    have : (1 : ℝ) + 1 / (m : ℝ) - 1 = 0 := by rw [h]; simp
    rw [add_sub_cancel_left] at this
    linarith
  have hlog : Real.log ((1 : ℝ) + 1 / (m : ℝ)) < 1 / (m : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos hbase hne
    rwa [add_sub_cancel_left] at h
  have hlog2 : Real.log (((1 : ℝ) + 1 / (m : ℝ)) ^ m) < 1 := by
    rw [Real.log_pow]
    calc (m : ℝ) * Real.log ((1 : ℝ) + 1 / (m : ℝ))
        < (m : ℝ) * (1 / (m : ℝ)) := by
          exact mul_lt_mul_of_pos_left hlog hmpos
      _ = 1 := by field_simp
  exact (Real.log_lt_iff_lt_exp (by positivity)).mp hlog2

/-- The one-variable Young inequality used in the Carleman induction step. -/
private lemma young_pow_le {v : ℝ} (hv : 0 ≤ v) {n : ℕ} (hn : 1 ≤ n) :
    v ^ n ≤ ((n : ℝ) / ((n : ℝ) + 1)) * v ^ (n + 1) + 1 / ((n : ℝ) + 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpq : (((n : ℝ) + 1) / (n : ℝ)).HolderConjugate ((n : ℝ) + 1) := by
    refine ⟨?_, by positivity, by positivity⟩
    rw [inv_one]
    field_simp
  have h := Real.young_inequality_of_nonneg (a := v ^ n) (b := 1)
    (pow_nonneg hv n) one_pos.le hpq
  have hrpow : (v ^ n : ℝ) ^ (((n : ℝ) + 1) / (n : ℝ)) = v ^ (n + 1) := by
    rw [← Real.rpow_natCast v n, ← Real.rpow_mul hv, ← Real.rpow_natCast v (n + 1)]
    congr 1
    push_cast
    rw [mul_comm, div_mul_cancel₀ _ hn0]
  have h1 : (1 : ℝ) ^ ((n : ℝ) + 1) = 1 := Real.one_rpow _
  rw [hrpow, h1, mul_one] at h
  have hdiv : v ^ (n + 1) / (((n : ℝ) + 1) / (n : ℝ))
      = ((n : ℝ) / ((n : ℝ) + 1)) * v ^ (n + 1) := by
    field_simp
  rw [hdiv] at h
  exact h

/-- The key one-variable estimate: for `u ≥ 0`,
`(n + 2) * u ^ n - n * u ^ (n + 1) ≤ e`. -/
private lemma carleman_key {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    ((n : ℝ) + 2) * u ^ n - (n : ℝ) * u ^ (n + 1) ≤ Real.exp 1 := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  set c := ((n : ℝ) + 2) / ((n : ℝ) + 1) with hc_def
  set v := u / c with hv_def
  have hcne : c ≠ 0 := by rw [hc_def]; positivity
  have hc_mul : c * ((n : ℝ) + 1) = (n : ℝ) + 2 := by
    rw [hc_def]; exact div_mul_cancel₀ _ hn1
  have hc_eq : c = (1 : ℝ) + 1 / ((((n + 1 : ℕ) : ℝ))) := by
    rw [hc_def]; push_cast; field_simp; ring
  have hcexp : c ^ (n + 1) < Real.exp 1 := by
    rw [hc_eq]; exact one_add_div_pow_lt_exp (m := n + 1) (by omega)
  have hu_eq : u = c * v := by
    rw [hv_def]; exact (mul_div_cancel₀ u hcne).symm
  have hv_nonneg : 0 ≤ v := by rw [hv_def]; positivity
  have hyoung := young_pow_le (v := v) hv_nonneg hn
  have hyoung' : ((n : ℝ) + 1) * v ^ n ≤ (n : ℝ) * v ^ (n + 1) + 1 := by
    have hmul := mul_le_mul_of_nonneg_left hyoung (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    have heq : ((n : ℝ) + 1) *
        (((n : ℝ) / ((n : ℝ) + 1)) * v ^ (n + 1) + 1 / ((n : ℝ) + 1))
        = (n : ℝ) * v ^ (n + 1) + 1 := by
      calc ((n : ℝ) + 1) *
            (((n : ℝ) / ((n : ℝ) + 1)) * v ^ (n + 1) + 1 / ((n : ℝ) + 1))
          = ((n : ℝ) + 1) * (((n : ℝ) / ((n : ℝ) + 1)) * v ^ (n + 1)) +
              ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by rw [mul_add]
        _ = (n : ℝ) * v ^ (n + 1) + 1 := by
            rw [← mul_assoc, mul_div_cancel₀ (n : ℝ) hn1, mul_one_div, div_self hn1]
    rw [heq] at hmul
    exact hmul
  have hident : ((n : ℝ) + 2) * u ^ n - (n : ℝ) * u ^ (n + 1)
      = c ^ (n + 1) * (((n : ℝ) + 1) * v ^ n - (n : ℝ) * v ^ (n + 1)) := by
    rw [hu_eq, mul_pow, mul_pow]
    have hD : c ^ (n + 1) * ((n : ℝ) + 1) = c ^ n * ((n : ℝ) + 2) := by
      rw [pow_succ, mul_assoc, hc_mul]
    linear_combination (-(v ^ n)) * hD
  calc ((n : ℝ) + 2) * u ^ n - (n : ℝ) * u ^ (n + 1)
      = c ^ (n + 1) * (((n : ℝ) + 1) * v ^ n - (n : ℝ) * v ^ (n + 1)) := hident
    _ ≤ c ^ (n + 1) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = c ^ (n + 1) := mul_one _
    _ ≤ Real.exp 1 := hcexp.le

/-- The Carleman induction step: one more geometric mean is controlled by the
previous geometric mean and the new term. -/
private lemma carleman_step {n : ℕ} (hn : 1 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((n : ℝ) + 2) * (x ^ n * y) ^ ((((n + 1 : ℕ) : ℝ))⁻¹)
      ≤ (n : ℝ) * x + Real.exp 1 * y := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · simp only [mul_zero, Real.zero_rpow (by positivity : ((((n + 1 : ℕ) : ℝ))⁻¹) ≠ 0),
      mul_zero, add_zero]
    exact mul_nonneg (by positivity) hx
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [zero_pow (by omega : n ≠ 0), zero_mul]
    simp only [mul_zero, Real.zero_rpow (by positivity : ((((n + 1 : ℕ) : ℝ))⁻¹) ≠ 0),
      mul_zero, zero_add]
    exact mul_nonneg (Real.exp_pos 1).le hy
  set u := (x / y) ^ ((((n + 1 : ℕ) : ℝ))⁻¹) with hu_def
  have hu_nonneg : 0 ≤ u := by
    rw [hu_def]
    exact Real.rpow_nonneg (div_nonneg hx hy) _
  have hG : (x ^ n * y) ^ ((((n + 1 : ℕ) : ℝ))⁻¹) = y * u ^ n := by
    have hprod : x ^ n * y = y ^ (n + 1) * (x / y) ^ n := by
      rw [div_pow, pow_succ y n]
      field_simp
    rw [hprod, Real.mul_rpow (pow_nonneg hy _)
      (pow_nonneg (div_nonneg hx hy) _)]
    have h1 : (y ^ (n + 1) : ℝ) ^ ((((n + 1 : ℕ) : ℝ))⁻¹) = y :=
      Real.pow_rpow_inv_natCast hy (by omega : n + 1 ≠ 0)
    have h2 : ((x / y) ^ n : ℝ) ^ ((((n + 1 : ℕ) : ℝ))⁻¹) = u ^ n := by
      rw [hu_def, ← Real.rpow_natCast (x / y) n,
        ← Real.rpow_mul (div_nonneg hx hy),
        ← Real.rpow_natCast ((x / y) ^ ((((n + 1 : ℕ) : ℝ))⁻¹)) n,
        ← Real.rpow_mul (div_nonneg hx hy)]
      rw [mul_comm]
    rw [h1, h2]
  have hx_eq : x = y * u ^ (n + 1) := by
    have h : u ^ (n + 1) = x / y := by
      rw [hu_def]
      exact Real.rpow_inv_natCast_pow (div_nonneg hx hy) (by omega : n + 1 ≠ 0)
    rw [h]
    field_simp
  have hkey := carleman_key hn hu_nonneg
  calc ((n : ℝ) + 2) * (x ^ n * y) ^ ((((n + 1 : ℕ) : ℝ))⁻¹)
      = ((n : ℝ) + 2) * (y * u ^ n) := by rw [hG]
    _ = y * (((n : ℝ) + 2) * u ^ n) := by ring
    _ ≤ y * ((n : ℝ) * u ^ (n + 1) + Real.exp 1) := by
        apply mul_le_mul_of_nonneg_left _ hy
        linarith
    _ = (n : ℝ) * (y * u ^ (n + 1)) + Real.exp 1 * y := by ring
    _ = (n : ℝ) * x + Real.exp 1 * y := by rw [← hx_eq]

/-- Strengthened finite Carleman inequality: the partial sum of the geometric
means plus `(M + 1)` times the last geometric mean is bounded by `e` times the
partial sum of the terms. -/
theorem carlemanGeomMean_sum_add_mul_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1), carlemanGeomMean a n) +
      ((M : ℝ) + 1) * carlemanGeomMean a M ≤
        Real.exp 1 * ∑ n ∈ Finset.range (M + 1), a n := by
  induction M with
  | zero =>
    rw [Finset.sum_range_one, Finset.sum_range_one, carlemanGeomMean_zero]
    push_cast
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h
      exact h
    calc a 0 + ((0 : ℝ) + 1) * a 0 = 2 * a 0 := by ring
      _ ≤ Real.exp 1 * a 0 := mul_le_mul_of_nonneg_right he (ha 0)
  | succ M IH =>
    have hstep := carleman_step (n := M + 1) (by omega)
      (carlemanGeomMean_nonneg ha M) (ha (M + 1))
    rw [← carlemanGeomMean_succ ha M] at hstep
    rw [Finset.sum_range_succ (f := carlemanGeomMean a) (n := M + 1),
      Finset.sum_range_succ (f := a) (n := M + 1)]
    push_cast at hstep IH ⊢
    linarith [IH, hstep]

/-- Finite Carleman inequality: the partial sum of the geometric means is
bounded by `e` times the partial sum of the terms. -/
theorem carlemanGeomMean_sum_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    (∑ n ∈ Finset.range N, carlemanGeomMean a n) ≤
      Real.exp 1 * ∑ n ∈ Finset.range N, a n := by
  cases N with
  | zero => simp
  | succ M =>
    have h := carlemanGeomMean_sum_add_mul_le ha M
    have hnonneg : 0 ≤ ((M : ℝ) + 1) * carlemanGeomMean a M :=
      mul_nonneg (by positivity) (carlemanGeomMean_nonneg ha M)
    linarith

/-- Carleman's inequality (sharp form): for a summable nonnegative sequence,
the series of geometric means of the initial products is summable and bounded
by `e` times the series of the terms. -/
theorem carleman_inequality {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hsumm : Summable a) :
    Summable (carlemanGeomMean a) ∧
      ∑' n, carlemanGeomMean a n ≤ Real.exp 1 * ∑' n, a n := by
  have hnonneg : ∀ n, 0 ≤ carlemanGeomMean a n := fun n => carlemanGeomMean_nonneg ha n
  have hbound : ∀ N, (∑ n ∈ Finset.range N, carlemanGeomMean a n) ≤
      Real.exp 1 * ∑' n, a n := by
    intro N
    calc (∑ n ∈ Finset.range N, carlemanGeomMean a n)
        ≤ Real.exp 1 * ∑ n ∈ Finset.range N, a n := carlemanGeomMean_sum_le ha N
      _ ≤ Real.exp 1 * ∑' n, a n := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
          exact hsumm.sum_le_tsum (Finset.range N) fun i _ => ha i
  exact ⟨summable_of_sum_range_le hnonneg hbound,
    Real.tsum_le_of_sum_range_le hnonneg hbound⟩

end

end MetaMathlibExt
