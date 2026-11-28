/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The logarithmic remainder argument is adapted from:

`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (Mathlib):
Copyright (c) 2018 Chris Hughes. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/

module

public import MathlibExt.NumberTheory.GobelSequence
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibExt.NumberTheory.GobelSequenceError
import MathlibExt.NumberTheory.GobelSequenceRootLimit
import MathlibExt.NumberTheory.GobelSequenceSomosBound
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Polynomial

/-!
# Asymptotic expansion of the Göbel sequence

For each natural number `k ≥ 2`, the Göbel sequences with parameters `(k, l)` for all
natural numbers `l ≥ 2` share an all-orders expansion in inverse powers of the index
`n`, after dividing out `C ^ (k ^ n) * n ^ (1 / (k - 1))`. The constant `C > 1`
may depend on both parameters.

## References

* Hibiki Gima, Toshiki Matsusaka, Taichi Miyazaki, and Shunta Yara,
  *On Integrality and Asymptotic Behavior of the (k, l)-Göbel Sequences*,
  Journal of Integer Sequences 27 (2024), Article 24.8.1, pp. 1–16, Theorem 4.
* Jonathan Sondow and Petros Hadjicostas,
  *The generalized-Euler-constant function γ(z) and a generalization of Somos's quadratic
  recurrence constant*, Journal of Mathematical Analysis and Applications 332 (2007),
  pp. 292–314, Theorem 9 and Lemma 1; see §3.3 and Theorem 15 of the preceding article.
* The logarithmic remainder estimate adapts `Real.abs_log_sub_add_sum_range_le` from
  `Mathlib.Analysis.SpecialFunctions.Log.Deriv` to the nonnegative real axis.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset Polynomial Set Topology

namespace GobelExpansion

private lemma log_remainder (R : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖Real.log (1 + x) - ∑ j ∈ range R, (-1 : ℝ) ^ j / (j + 1) * x ^ (j + 1)‖ ≤
      x ^ (R + 1) := by
  let f (y : ℝ) := Real.log (1 + y) - ∑ j ∈ range R, (-1 : ℝ) ^ j / (j + 1) * y ^ (j + 1)
  have hd (y : ℝ) (hy : y ∈ Icc 0 x) : HasDerivAt f ((-y) ^ R / (1 + y)) y := by
    have hy' : 0 < 1 + y := by linarith [hy.1]
    have hterm (j : ℕ) : HasDerivAt
        (fun z : ℝ => (-1 : ℝ) ^ j / (j + 1) * z ^ (j + 1)) ((-y) ^ j) y := by
      convert ((hasDerivAt_pow (j + 1) y).const_mul ((-1 : ℝ) ^ j / (j + 1))) using 1
      rw [Nat.cast_succ, Nat.add_sub_cancel, neg_eq_neg_one_mul y, mul_pow]
      have hj : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y := by
      simpa using ((hasDerivAt_id y).const_add 1).log hy'.ne'
    have hgeom := geom_sum_mul_neg (-y) R
    have hderiv : 1 / (1 + y) - ∑ j ∈ range R, (-y) ^ j = (-y) ^ R / (1 + y) := by
      apply (eq_div_iff hy'.ne').mpr
      rw [sub_mul, div_mul_cancel₀ _ hy'.ne']
      linarith only [hgeom]
    rw [← hderiv]
    exact hlog.sub (.fun_sum fun j _ => hterm j)
  have hb (y : ℝ) (hy : y ∈ Icc 0 x) : ‖(-y) ^ R / (1 + y)‖ ≤ x ^ R := by
    have hy' : 0 ≤ y := hy.1
    rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg hy',
      Real.norm_of_nonneg (by positivity : 0 ≤ 1 + y)]
    exact (div_le_self (by positivity) (by linarith)).trans (pow_le_pow_left₀ hy' hy.2 _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt) hb (convex_Icc 0 x) (left_mem_Icc.mpr hx)
    (right_mem_Icc.mpr hx)
  simpa [f, Real.norm_of_nonneg hx, pow_succ] using h

private noncomputable def moment (k j : ℕ) : ℝ :=
  ∑' m : ℕ, (m + 1 : ℝ) ^ j / (k : ℝ) ^ (m + 1)

private lemma summable_moment {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    Summable (fun m : ℕ => (m + 1 : ℝ) ^ j / (k : ℝ) ^ (m + 1)) := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hr : ‖(k : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ hk'
  have hs := summable_pow_mul_geometric_of_norm_lt_one j hr
  have hshift := (summable_nat_add_iff 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, inv_pow, div_eq_mul_inv] using hshift

private lemma weight_sum {k : ℕ} (hk : 2 ≤ k) :
    (∑' m : ℕ, ((k : ℝ) ^ (m + 1))⁻¹) = 1 / ((k : ℝ) - 1) := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hkr : 0 < (k : ℝ) := zero_lt_one.trans hk'
  have hr := inv_lt_one_of_one_lt₀ hk'
  simp_rw [← inv_pow, pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) hr]
  field_simp

private noncomputable def logSeries (k : ℕ) (x : ℝ) : ℝ :=
  ∑' m : ℕ, Real.log (1 + (m + 1 : ℝ) * x) / (k : ℝ) ^ (m + 1)

private noncomputable def logPoly (k R : ℕ) : ℝ[X] :=
  ∑ j ∈ range R, monomial (j + 1) ((-1 : ℝ) ^ j / (j + 1) * moment k (j + 1))

private lemma summable_logSeries {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun m : ℕ => Real.log (1 + (m + 1 : ℝ) * x) / (k : ℝ) ^ (m + 1)) := by
  refine ((summable_moment hk 1).mul_right x).of_nonneg_of_le (fun m => ?_) (fun m => ?_)
  · exact div_nonneg (Real.log_nonneg (by linarith [show 0 ≤ (m + 1 : ℝ) * x by positivity]))
      (by positivity)
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (m + 1 : ℝ) * x by positivity)
    rw [pow_one, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private lemma logPoly_remainder {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖logSeries k x - (logPoly k R).eval x‖ ≤ moment k (R + 1) * x ^ (R + 1) := by
  let f (m : ℕ) := Real.log (1 + (m + 1 : ℝ) * x) / (k : ℝ) ^ (m + 1)
  let g (j m : ℕ) := (-1 : ℝ) ^ j / (j + 1) * ((m + 1 : ℝ) ^ (j + 1) /
    (k : ℝ) ^ (m + 1)) * x ^ (j + 1)
  have hg (j : ℕ) : Summable (g j) := ((summable_moment hk (j + 1)).mul_left _).mul_right _
  have hf : Summable f := summable_logSeries hk hx
  have hsum : (logPoly k R).eval x = ∑' m : ℕ, ∑ j ∈ range R, g j m := by
    rw [Summable.tsum_finsetSum (fun j _ => hg j)]
    simp only [logPoly, eval_finsetSum, eval_monomial, g, (summable_moment hk _).tsum_mul_left,
      ((summable_moment hk _).mul_left _).tsum_mul_right, moment]
  have hgs : Summable (fun m => ∑ j ∈ range R, g j m) :=
    (hasSum_sum fun j _ => (hg j).hasSum).summable
  rw [show logSeries k x = ∑' m, f m from rfl, hsum, ← hf.tsum_sub hgs, moment,
    ← (summable_moment hk _).tsum_mul_right]
  have hbound (m : ℕ) : ‖f m - ∑ j ∈ range R, g j m‖ ≤
      (m + 1 : ℝ) ^ (R + 1) / (k : ℝ) ^ (m + 1) * x ^ (R + 1) := by
    have heq : (∑ j ∈ range R, g j m) =
        (∑ j ∈ range R, (-1 : ℝ) ^ j / (j + 1) * ((m + 1 : ℝ) * x) ^ (j + 1)) /
          (k : ℝ) ^ (m + 1) := by
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro j _
      simp only [g, mul_pow]
      ring
    rw [heq, show f m = Real.log (1 + (m + 1 : ℝ) * x) / (k : ℝ) ^ (m + 1) from rfl,
      ← sub_div, norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ (k : ℝ) ^ (m + 1)),
      div_mul_eq_mul_div, ← mul_pow]
    exact div_le_div_of_nonneg_right (log_remainder R (by positivity)) (by positivity)
  have hM := (summable_moment hk (R + 1)).mul_right (x ^ (R + 1))
  have hs := hM.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hbound hM)

private lemma logPoly_coeff (k R j : ℕ) : (logPoly k R).coeff (j + 1) =
    if j < R then (-1 : ℝ) ^ j / (j + 1) * moment k (j + 1) else 0 := by
  rw [logPoly, finsetSum_coeff]
  by_cases hj : j < R
  · rw [ite_eq_left hj, Finset.sum_eq_single_of_mem j (mem_range.mpr hj)]
    · simp
    · intro i _ hij
      rw [coeff_monomial_apply, ite_eq_right (by omega)]
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_monomial_apply, ite_eq_right (by have := mem_range.mp hi; omega)]

private lemma logPoly_coeff_zero (k R : ℕ) : (logPoly k R).coeff 0 = 0 := by
  simp [logPoly]

private noncomputable def expPoly (k R : ℕ) : ℝ[X] :=
  ∑ h ∈ range (R + 1), C (1 / (h.factorial : ℝ)) * logPoly k R ^ h

private lemma expPoly_coeff (k : ℕ) {r R : ℕ} (hr : r ≤ R) :
    (expPoly k R).coeff r = (expPoly k r).coeff r := by
  have hdiv : (X : ℝ[X]) ^ (r + 1) ∣ logPoly k R - logPoly k r := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    rw [coeff_sub, sub_eq_zero]
    cases d with
    | zero => simp only [logPoly_coeff_zero]
    | succ j => rw [logPoly_coeff, logPoly_coeff, ite_eq_left (by omega), ite_eq_left (by omega)]
  have hX : (X : ℝ[X]) ∣ logPoly k R := X_dvd_iff.mpr (logPoly_coeff_zero k R)
  simp only [expPoly, finsetSum_coeff, coeff_C_mul]
  calc
    _ = ∑ h ∈ range (r + 1), 1 / (h.factorial : ℝ) * (logPoly k R ^ h).coeff r := by
      symm
      apply Finset.sum_subset (range_mono (by omega))
      intro h _ hh
      have hpow := pow_dvd_pow_of_dvd_of_le hX (show r + 1 ≤ h by simpa using hh)
      rw [X_pow_dvd_iff.mp hpow r (by omega), mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      have hd := X_pow_dvd_iff.mp (hdiv.trans (sub_dvd_pow_sub_pow _ _ h)) r (by omega)
      rw [coeff_sub, sub_eq_zero] at hd
      rw [hd]

private lemma eval_isBigO_of_X_pow_dvd {p : ℝ[X]} {N : ℕ} (hp : (X : ℝ[X]) ^ N ∣ p) :
    p.eval =O[𝓝 0] (fun x : ℝ => x ^ N) := by
  obtain ⟨q, rfl⟩ := hp
  have hq : q.eval =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto q.continuous.continuousAt.tendsto one_ne_zero
  simpa only [eval_mul, eval_pow, eval_X, mul_one] using
    ((isBigO_refl (fun x : ℝ => x ^ N) (𝓝 0)).mul hq)

private noncomputable def coeff (k r : ℕ) : ℝ := (expPoly k r).coeff r

private lemma coeff_zero (k : ℕ) : coeff k 0 = 1 := by
  simp [coeff, expPoly]

private lemma expPoly_sub_truncation (k R : ℕ) :
    (fun x : ℝ => (expPoly k R).eval x - ∑ r ∈ range (R + 1), coeff k r * x ^ r)
      =O[𝓝 0] (fun x : ℝ => x ^ (R + 1)) := by
  let p : ℝ[X] := ∑ r ∈ range (R + 1), monomial r (coeff k r)
  have h : (X : ℝ[X]) ^ (R + 1) ∣ expPoly k R - p := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    rw [coeff_sub, sub_eq_zero, expPoly_coeff k (by omega : d ≤ R)]
    change coeff k d = p.coeff d
    dsimp only [p]
    rw [finsetSum_coeff, Finset.sum_eq_single_of_mem d (mem_range.mpr hd)]
    · simp
    · intro r _ hr
      rw [coeff_monomial_apply, ite_eq_right hr]
  simpa only [eval_sub, p, eval_finsetSum, eval_monomial] using eval_isBigO_of_X_pow_dvd h

private lemma exp_logSeries_isBigO {k : ℕ} (hk : 2 ≤ k) (R : ℕ) :
    (fun x : ℝ => Real.exp (logSeries k x) - ∑ r ∈ range (R + 1), coeff k r * x ^ r)
      =O[𝓝[Set.Ici 0] 0] (fun x : ℝ => x ^ (R + 1)) := by
  let p := logPoly k R
  let F : Filter ℝ := 𝓝[Set.Ici 0] 0
  have hle : F ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hlog : (fun x : ℝ => logSeries k x - p.eval x) =O[F] (fun x : ℝ => x ^ (R + 1)) := by
    refine IsBigO.of_bound (moment k (R + 1)) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (by simpa only [Real.norm_of_nonneg (pow_nonneg hx (R + 1))] using
      logPoly_remainder hk R hx)
  have hp : p.eval =O[F] (fun x : ℝ => x) := by
    have hX : (X : ℝ[X]) ^ 1 ∣ p := by
      rw [pow_one, X_dvd_iff]
      exact logPoly_coeff_zero k R
    simpa only [pow_one] using (eval_isBigO_of_X_pow_dvd hX).mono hle
  have hId : Tendsto (fun x : ℝ => x) F (𝓝 0) := hle
  have ht : Tendsto p.eval F (𝓝 0) := hp.trans_tendsto hId
  have hd : Tendsto (fun x => logSeries k x - p.eval x) F (𝓝 0) := by
    apply hlog.trans_tendsto
    simpa only [zero_pow (Nat.succ_ne_zero R)] using hId.pow (R + 1)
  have hexp : (fun x => Real.exp (logSeries k x) - Real.exp (p.eval x))
      =O[F] (fun x : ℝ => x ^ (R + 1)) := by
    have h := (Real.exp_sub_sum_range_isBigO_pow 1).comp_tendsto hd
    have h' : (fun x => Real.exp (logSeries k x - p.eval x) - 1)
        =O[F] (fun x : ℝ => x ^ (R + 1)) := by
      apply IsBigO.trans _ hlog
      simpa [Function.comp_def] using h
    have hbounded : (fun x => Real.exp (p.eval x)) =O[F] (fun _ : ℝ => (1 : ℝ)) :=
      isBigO_const_of_tendsto (Real.continuous_exp.continuousAt.tendsto.comp ht) one_ne_zero
    refine (hbounded.mul h').congr (fun x => ?_) (fun x => one_mul _)
    rw [mul_sub, mul_one, ← Real.exp_add, add_sub_cancel]
  have hpoly : (fun x => Real.exp (p.eval x) - (expPoly k R).eval x)
      =O[F] (fun x : ℝ => x ^ (R + 1)) := by
    have h := (Real.exp_sub_sum_range_isBigO_pow (R + 1)).comp_tendsto ht
    simp only [Function.comp_def] at h
    have heval (x : ℝ) :
        (expPoly k R).eval x = ∑ i ∈ range (R + 1), p.eval x ^ i / (i.factorial : ℝ) := by
      simp only [expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, p, div_eq_mul_inv, one_mul]
      exact sum_congr rfl fun i _ => mul_comm _ _
    simpa only [heval] using h.trans (hp.pow (R + 1))
  refine ((hexp.add hpoly).add ((expPoly_sub_truncation k R).mono hle)).congr
    (fun x => ?_) (fun _ => rfl)
  ring

private lemma exp_log_sum_eq {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)) =
      (n : ℝ) ^ ((1 : ℝ) / (k - 1)) * Real.exp (logSeries k (n : ℝ)⁻¹) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hterm (m : ℕ) : Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1) =
      Real.log n * ((k : ℝ) ^ (m + 1))⁻¹ +
        Real.log (1 + (m + 1 : ℝ) * (n : ℝ)⁻¹) / (k : ℝ) ^ (m + 1) := by
    have he : (m + 1 : ℝ) + n = n * (1 + (m + 1 : ℝ) * (n : ℝ)⁻¹) := by
      field_simp
      ring
    rw [he, Real.log_mul hn'.ne' (by positivity), add_div, div_eq_mul_inv (Real.log n)]
  have hs : Summable (fun m : ℕ => ((k : ℝ) ^ (m + 1))⁻¹) := by
    simpa only [pow_zero, one_div] using summable_moment hk 0
  simp_rw [hterm]
  rw [(hs.mul_left (Real.log n)).tsum_add (summable_logSeries hk (by positivity)),
    hs.tsum_mul_left, weight_sum hk, Real.exp_add, Real.rpow_def_of_pos hn']
  rfl

private lemma invNat_tendsto : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[Set.Ici 0] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop
    (R := ℝ)), Eventually.of_forall (fun n => mem_Ici.mpr (by positivity))⟩

private lemma exp_log_sum_isBigO {k : ℕ} (hk : 2 ≤ k) (R : ℕ) :
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)) -
      (n : ℝ) ^ ((1 : ℝ) / (k - 1)) * (1 + ∑ r ∈ Icc 1 R, coeff k r / (n : ℝ) ^ r))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (k - 1)) / (n : ℝ) ^ (R + 1)) := by
  have h := (exp_logSeries_isBigO hk R).comp_tendsto invNat_tendsto
  have hn := isBigO_refl (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (k - 1))) atTop
  refine (hn.mul h).congr' ?_ (Eventually.of_forall (fun n => ?_))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hs : (∑ r ∈ range (R + 1), coeff k r * ((n : ℝ)⁻¹) ^ r) =
        1 + ∑ r ∈ Icc 1 R, coeff k r / (n : ℝ) ^ r := by
      rw [show Finset.Icc 1 R = (range (R + 1)).erase 0 by
        ext r
        simp only [Finset.mem_Icc, mem_erase, Finset.mem_range]
        omega, ← sum_erase_add _ _ (mem_range.mpr (Nat.succ_pos R))]
      simp only [coeff_zero, pow_zero, mul_one, inv_pow, div_eq_mul_inv]
      exact add_comm _ _
    simp only [Function.comp_def, hs, exp_log_sum_eq hk hn, mul_sub]
  · simp only [Function.comp_def, inv_pow, div_eq_mul_inv]

end GobelExpansion

open GobelExpansion in
/-- **Asymptotic expansion of the $(k, l)$-Göbel sequence.** Let $k, l \ge 2$ be natural numbers
and let $g_{k,l}$ be the $(k, l)$-Göbel sequence. There are real numbers $a_1, a_2, \dots$ depending
only on $k$, and a real number $C > 1$ that may depend on both $k$ and $l$, such that for every
natural number $R$, as $n \to \infty$,

$$g_{k,l}(n) - C^{k^n} n^{1/(k-1)} \Bigl(1 + \sum_{r=1}^{R} \frac{a_r}{n^r}\Bigr) =
O\Bigl(\frac{C^{k^n} n^{1/(k-1)}}{n^{R+1}}\Bigr).$$

In other words, $g_{k,l}(n) \sim C^{k^n} n^{1/(k-1)} \bigl(1 + \sum_{r \ge 1} a_r / n^r\bigr)$ as
an asymptotic expansion, generalizing Zagier's asymptotic for Göbel's sequence.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 4 (`jis-2024-24.8.1-thm-4`). -/
public theorem gobelSequence_asymptotic_expansion (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : ℕ → ℝ, ∀ l : ℕ, 2 ≤ l → ∃ C : ℝ, 1 < C ∧ ∀ R : ℕ,
      (fun n : ℕ => (gobelSequence k l n : ℝ)
          - C ^ (k ^ n) * (n : ℝ) ^ ((1 : ℝ) / (k - 1))
            * (1 + ∑ r ∈ Finset.Icc 1 R, a r / (n : ℝ) ^ r))
        =O[atTop]
      (fun n : ℕ => C ^ (k ^ n) * (n : ℝ) ^ ((1 : ℝ) / (k - 1)) / (n : ℝ) ^ (R + 1)) := by
  refine ⟨GobelExpansion.coeff k, fun l hl => ?_⟩
  obtain ⟨C, hC, hlim⟩ := gobelSequence_root_tendsto_gt_one k l hk hl
  refine ⟨C, hC, fun R => ?_⟩
  let E (n : ℕ) := Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
  let A (n : ℕ) := (n : ℝ) ^ ((1 : ℝ) / (k - 1))
  let d (n : ℕ) := (n : ℝ) ^ (R + 1)
  have herr : (fun n : ℕ => (gobelSequence k l n : ℝ) / C ^ (k ^ n) - E n)
      =O[atTop] (fun n : ℕ => (d n)⁻¹) := by
    refine (gobelSequence_error_isBigO k l hk hl C hlim ((R + 1 : ℕ) : ℝ) (by positivity)).neg_left
      |>.congr' ?_ (Eventually.of_forall (fun n => ?_))
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hg : 0 ≤ (gobelSequence k l n : ℝ) := by
        simpa using somosLike_le_gobelSequence k l hk hl (fun _ => 0)
          (by simp [zero_pow (show k ≠ 0 by omega)]) (by simp [zero_pow (show k ≠ 0 by omega)]) n hn
      have hp : k ^ n ≠ 0 := pow_ne_zero _ (by omega)
      simp only [E, neg_sub, div_pow, one_div, ← Nat.cast_pow, Real.rpow_inv_natCast_pow hg hp]
    · change (n : ℝ) ^ (-((R + 1 : ℕ) : ℝ)) = ((n : ℝ) ^ (R + 1))⁻¹
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hscale : (fun n : ℕ => (d n)⁻¹) =O[atTop] (fun n : ℕ => A n / d n) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hAn : 1 ≤ A n := Real.one_le_rpow (by exact_mod_cast hn)
      (div_nonneg zero_le_one (sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ k by omega))))
    simp only [norm_inv, one_mul, norm_div, Real.norm_of_nonneg (zero_le_one.trans hAn)]
    simpa only [one_div] using div_le_div_of_nonneg_right hAn (norm_nonneg (d n))
  have hE := exp_log_sum_isBigO hk R
  have htot := (herr.trans hscale).add hE
  refine ((isBigO_refl (fun n : ℕ => C ^ (k ^ n)) atTop).mul htot).congr
    (fun n => ?_) (fun n => ?_)
  · simp only [E]
    field_simp [ne_of_gt (zero_lt_one.trans hC)]
    ring
  · simp only [A, d, mul_div_assoc]

end MetaMathlibExt
