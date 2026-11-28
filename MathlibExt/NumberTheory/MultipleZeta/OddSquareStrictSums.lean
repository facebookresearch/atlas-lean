/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.NumberTheory.MultipleZeta.Series

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Finset.Sort
import Mathlib.Data.PNat.Basic

/-!
# Strictly nested sums of reciprocal odd squares

For every natural number `k`, the sum of the products of reciprocal odd squares over strictly
ordered `k`-tuples of positive indices is `(π / 2) ^ (2 * k) / (2 * k)!`. The empty tuple gives
`1` at `k = 0`, as in the convention used in the source's proof.

The proof uses the cosine product obtained by separating the odd factors in Euler's sine product.
Grouping its expansion by the cardinality of the chosen finite subset gives the even Taylor
coefficients of cosine.

## References

* Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26 (2026),
  Article A114, pp. 5–6, Corollary 2.
* Leonhard Euler, *Introductio in analysin infinitorum*, vol. I, Marcum-Michaelem Bousquet & Socios
  (1748), Chapter IX, §158, for the trigonometric product formulas.
-/

open Filter Finset FormalMultilinearSeries
open scoped ENNReal Topology

namespace MetaMathlibExt

namespace OddSquareStrictSums

private noncomputable def oddWeight (n : ℕ) : ℝ := ((2 * (n : ℝ) + 1) ^ 2)⁻¹

private noncomputable def subsetSum (k : ℕ) : ℝ :=
  ∑' s : {s : Finset ℕ // s.card = k}, ∏ n ∈ s.1, oddWeight n

private lemma summable_oddWeight : Summable oddWeight := by
  have h := (Real.summable_nat_pow_inv (p := 2)).2 (by decide)
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) :=
    (add_left_injective 1).comp (mul_right_injective₀ (by decide))
  change Summable (fun n : ℕ => ((2 * (n : ℝ) + 1) ^ 2)⁻¹)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using h.comp_injective hinj

private lemma hasProd_sineFactors {x : ℝ} (hx : x ≠ 0) :
    HasProd (fun n : ℕ => 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2)
      (Real.sin (Real.pi * x) / (Real.pi * x)) := by
  have hs : Summable (fun n : ℕ => -(x ^ 2 / ((n : ℝ) + 1) ^ 2)) := by
    apply Summable.of_norm
    simpa only [norm_neg, Nat.cast_one] using summable_pow_div_add (x ^ 2) 2 1 (by decide)
  have hp : Multipliable (fun n : ℕ => 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs
  apply hp.hasProd_iff_tendsto_nat.mpr
  have hxπ := mul_ne_zero Real.pi_ne_zero hx
  simpa only [← mul_assoc, inv_mul_cancel₀ hxπ, one_mul, div_eq_inv_mul] using
    (Real.tendsto_euler_sin_prod x).const_mul (Real.pi * x)⁻¹

private lemma odd_product_value {x a : ℝ} (hx : |x| ≤ 1)
    (ha : HasProd (fun n => 1 + (-(x ^ 2)) * oddWeight n) a) :
    a = Real.cos (Real.pi / 2 * x) := by
  by_cases hx₀ : x = 0
  · subst x
    simpa using (by simpa using ha : HasProd (fun _ : ℕ => (1 : ℝ)) a).unique hasProd_one
  have hx₂ : x / 2 ≠ 0 := div_ne_zero hx₀ (by norm_num)
  have hEven : HasProd (fun n : ℕ => 1 - x ^ 2 / (((2 * n + 1 : ℕ) : ℝ) + 1) ^ 2)
      (Real.sin (Real.pi * (x / 2)) / (Real.pi * (x / 2))) := by
    apply (hasProd_sineFactors hx₂).congr_fun
    intro n
    rw [show (((2 * n + 1 : ℕ) : ℝ) + 1) = 2 * ((n : ℝ) + 1) by push_cast; ring,
      mul_pow, div_pow, div_div]
  have hOdd : HasProd (fun n : ℕ => 1 - x ^ 2 / (((2 * n : ℕ) : ℝ) + 1) ^ 2) a := by
    apply ha.congr_fun
    intro n
    simp only [oddWeight, Nat.cast_mul, Nat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv, neg_mul]
  have hf : a * (Real.sin (Real.pi * (x / 2)) / (Real.pi * (x / 2))) =
      Real.sin (Real.pi * x) / (Real.pi * x) :=
    (hOdd.even_mul_odd hEven).unique (hasProd_sineFactors hx₀)
  have harg : Real.pi * (x / 2) ≠ 0 := mul_ne_zero Real.pi_ne_zero hx₂
  have hsin : Real.sin (Real.pi * (x / 2)) ≠ 0 := by
    have habs : |Real.pi * (x / 2)| < Real.pi := by
      rw [abs_mul, abs_of_nonneg Real.pi_pos.le, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (mul_lt_mul_of_pos_left (by linarith) Real.pi_pos).trans_eq (mul_one _)
    obtain ⟨hl, hu⟩ := abs_lt.mp habs
    exact (Real.sin_eq_zero_iff_of_lt_of_lt hl hu).ne.mpr harg
  apply mul_right_cancel₀ (div_ne_zero hsin harg)
  rw [hf, show Real.pi * x = 2 * (Real.pi * (x / 2)) by ring, Real.sin_two_mul]
  rw [show Real.pi / 2 * x = Real.pi * (x / 2) by ring]
  field_simp

private lemma hasSum_subsetSum_cos {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => ((-1 : ℝ) ^ k * subsetSum k) * x ^ (2 * k))
      (Real.cos (Real.pi / 2 * x)) := by
  let f (n : ℕ) := -(x ^ 2) * oddWeight n
  have hS : Summable (fun s : Finset ℕ => ∏ n ∈ s, f n) :=
    summable_finsetProd_of_summable_norm (summable_oddWeight.mul_left (-(x ^ 2))).norm
  have hP : HasProd (fun n => 1 + f n) (∑' s : Finset ℕ, ∏ n ∈ s, f n) :=
    hasProd_one_add_of_hasSum_prod hS.hasSum
  have hcos := odd_product_value hx hP
  rw [← hcos]
  refine (hS.hasSum.tsum_fiberwise Finset.card).congr_fun fun k => ?_
  change ((-1 : ℝ) ^ k * subsetSum k) * x ^ (2 * k) =
    ∑' s : {s : Finset ℕ // s.card = k}, ∏ n ∈ s.1, f n
  rw [subsetSum, mul_right_comm, ← tsum_mul_left]
  refine tsum_congr fun s => ?_
  have hpow : (-(x ^ 2)) ^ k = (-1 : ℝ) ^ k * x ^ (2 * k) := by
    rw [pow_mul, ← mul_pow, neg_one_mul]
  simp only [f, Finset.prod_mul_distrib, Finset.prod_const, s.2, hpow]

private noncomputable def evenCoeffs (c : ℕ → ℝ) : ℕ → ℝ :=
  Function.extend (fun k => 2 * k) c 0

private lemma evenCoeffs_two_mul (c : ℕ → ℝ) (k : ℕ) : evenCoeffs c (2 * k) = c k :=
  (mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)).extend_apply c 0 k

private lemma hasSum_evenCoeffs {c : ℕ → ℝ} {x a : ℝ}
    (h : HasSum (fun k => c k * x ^ (2 * k)) a) :
    HasSum (fun n => evenCoeffs c n * x ^ n) a := by
  have hi : Function.Injective (fun k : ℕ => 2 * k) := mul_right_injective₀ (by decide)
  refine ((hasSum_extend_zero hi).2 h).congr_fun fun n => ?_
  by_cases hn : ∃ k, 2 * k = n
  · obtain ⟨k, rfl⟩ := hn
    simp only [evenCoeffs_two_mul, hi.extend_apply]
  · simp only [evenCoeffs, Function.extend_apply' _ _ _ hn, Pi.zero_apply, zero_mul]

private lemma hasFPowerSeriesAt_of_hasSum_unit {c : ℕ → ℝ} {f : ℝ → ℝ}
    (h : ∀ x : ℝ, |x| ≤ 1 → HasSum (fun n => c n * x ^ n) (f x)) :
    HasFPowerSeriesAt f (ofScalars ℝ c) 0 := by
  have h₁ : Summable c := by simpa using (h 1 (by norm_num)).summable
  have hRadius : (1 : ℝ≥0∞) ≤ (ofScalars ℝ c).radius := by
    simpa only [ENNReal.coe_one] using
      (ofScalars ℝ c).le_radius_of_summable (r := 1) (by simpa using h₁.norm)
  have hp := (ofScalars ℝ c).hasFPowerSeriesOnBall (zero_lt_one.trans_le hRadius)
  apply hp.hasFPowerSeriesAt.congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (zero_lt_one : (0 : ℝ) < 1)] with x hx
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
  change ofScalarsSum c x = f x
  simpa only [ofScalars_sum_eq, smul_eq_mul] using (h x hx.le).tsum_eq

private lemma subsetSum_eq (k : ℕ) : subsetSum k = (Real.pi / 2) ^ (2 * k) / (2 * k).factorial := by
  let a : ℕ → ℝ := fun k => (-1) ^ k * subsetSum k
  let b : ℕ → ℝ := fun k => (-1) ^ k * (Real.pi / 2) ^ (2 * k) / (2 * k).factorial
  have ha : HasFPowerSeriesAt (fun x => Real.cos (Real.pi / 2 * x))
      (ofScalars ℝ (evenCoeffs a)) 0 :=
    hasFPowerSeriesAt_of_hasSum_unit fun _ hx => hasSum_evenCoeffs (hasSum_subsetSum_cos hx)
  have hb : HasFPowerSeriesAt (fun x => Real.cos (Real.pi / 2 * x))
      (ofScalars ℝ (evenCoeffs b)) 0 := by
    apply hasFPowerSeriesAt_of_hasSum_unit
    intro x _
    refine hasSum_evenCoeffs ((Real.hasSum_cos (Real.pi / 2 * x)).congr_fun fun j => ?_)
    simp only [b, mul_pow]
    ring
  have hab := congrFun (ofScalars_series_injective ℝ ℝ (ha.eq_formalMultilinearSeries hb)) (2 * k)
  simp only [evenCoeffs_two_mul, a, b] at hab
  apply mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℝ) ≠ 0))
  simpa [mul_div_assoc] using hab

private def finsetOfTuple {k : ℕ} (m : MultipleZeta.StrictDecreasingTuple k) :
    {s : Finset ℕ // s.card = k} :=
  ⟨Finset.univ.image (PNat.natPred ∘ m.1), by
    rw [Finset.card_image_of_injective _ (PNat.natPred_injective.comp m.2.injective),
      Finset.card_univ, Fintype.card_fin]⟩

private noncomputable def tupleEquiv (k : ℕ) :
    MultipleZeta.StrictDecreasingTuple k ≃ {s : Finset ℕ // s.card = k} where
  toFun := finsetOfTuple
  invFun s := ⟨fun j => (s.1.orderEmbOfFin s.2 j.rev).succPNat,
    Nat.succPNat_strictMono.comp_strictAnti
      ((s.1.orderEmbOfFin s.2).strictMono.comp_strictAnti Fin.rev_strictAnti)⟩
  left_inv m := by
    have hmono : StrictMono (fun j : Fin k => (m.1 j.rev).natPred) :=
      fun _ _ hij => PNat.natPred_strictMono (m.2 (Fin.rev_strictAnti hij))
    have he := Finset.orderEmbOfFin_unique (finsetOfTuple m).2
      (fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j.rev)) hmono
    apply Subtype.ext
    funext j
    change ((finsetOfTuple m).1.orderEmbOfFin (finsetOfTuple m).2 j.rev).succPNat = m.1 j
    rw [← congrFun he j.rev, Fin.rev_rev, Function.comp_apply, PNat.succPNat_natPred]
  right_inv s := by
    apply Subtype.ext
    refine Finset.eq_of_subset_of_card_le ?_ (s.2.trans_le (finsetOfTuple _).2.ge)
    intro n hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hn
    change ((s.1.orderEmbOfFin s.2 j.rev).succPNat).natPred ∈ s.1
    rw [Nat.natPred_succPNat]
    exact Finset.orderEmbOfFin_mem _ _ _

private lemma tsum_tuple_eq_subsetSum (k : ℕ) :
    ∑' m : MultipleZeta.StrictDecreasingTuple k,
        ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ = subsetSum k := by
  rw [subsetSum, ← (tupleEquiv k).tsum_eq]
  refine tsum_congr fun m => ?_
  change (∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹) =
    ∏ n ∈ Finset.univ.image (PNat.natPred ∘ m.1), oddWeight n
  rw [Finset.prod_image (PNat.natPred_injective.comp m.2.injective).injOn]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : ((m.1 j).natPred : ℝ) + 1 = ((m.1 j : ℕ) : ℝ) := by
    exact_mod_cast (m.1 j).natPred_add_one
  unfold oddWeight
  rw [show 2 * ((m.1 j : ℕ) : ℝ) - 1 = 2 * ((m.1 j).natPred : ℝ) + 1 by linarith]
  rfl

end OddSquareStrictSums

/-- **Strictly nested sums of reciprocal odd squares.** For every natural number $k$,
$$\sum_{i_1 > i_2 > \cdots > i_k \ge 1} \prod_{j=1}^{k} \frac{1}{(2 i_j - 1)^2} =
\frac{(\pi/2)^{2k}}{(2k)!},$$
where the sum runs over all strictly decreasing $k$-tuples $(i_1, \ldots, i_k)$ of positive
integers. For $k = 0$ the sum has the single empty term and both sides equal $1$.

The source states the identity for $k > 0$; the case $k = 0$ is included here.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Corollary 2. -/
public theorem tsum_strictDecreasing_prod_inv_odd_sq_eq (k : ℕ) :
    ∑' m : MultipleZeta.StrictDecreasingTuple k,
        ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ =
      (Real.pi / 2) ^ (2 * k) / (2 * k).factorial := by
  cases k with
  | zero =>
    rw [tsum_eq_single MultipleZeta.StrictDecreasingTuple.empty]
    · simp
    · intro m hm
      exact (hm m.eq_empty).elim
  | succ k => rw [OddSquareStrictSums.tsum_tuple_eq_subsetSum, OddSquareStrictSums.subsetSum_eq]

end MetaMathlibExt
