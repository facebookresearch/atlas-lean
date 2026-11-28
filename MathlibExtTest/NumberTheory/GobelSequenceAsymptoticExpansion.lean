/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequenceAsymptoticExpansion
import MathlibExt.NumberTheory.GobelSequenceError
import MathlibExt.NumberTheory.GobelSequenceRootLimit
import MathlibExt.NumberTheory.GobelSequenceSomosBound
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed

namespace MetaMathlibExt

open Asymptotics Filter Finset Topology

-- Independently estimate the quadratic truncation using the log-ratio series
-- with argument x / (x + 2), which is less than one even when x is large.
private lemma log_quadratic_bound {x : ℝ} (hx : 0 ≤ x) :
    ‖Real.log (1 + x) - (x - x ^ 2 / 2)‖ ≤ x ^ 3 := by
  let y := x / (x + 2)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hratio : (1 + y) / (1 - y) = 1 + x := by
    have h : 1 - y ≠ 0 := (sub_pos.mpr hy').ne'
    apply (div_eq_iff h).mpr
    dsimp [y]
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div hy hy' 1
  have hhi := Real.log_div_le_sum_range_add hy hy' 1
  norm_num [hratio] at hlo hhi
  have hdiff : 2 * y - (x - x ^ 2 / 2) = x ^ 3 / (2 * (x + 2)) := by
    dsimp [y]
    field_simp
    ring
  have htail : y ^ 3 / (1 - y ^ 2) = x ^ 3 / (4 * (x + 2) * (1 + x)) := by
    have h : 0 < 1 - y ^ 2 := by
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hy'.le)]
    apply (div_eq_div_iff h.ne' (by positivity)).2
    dsimp [y]
    field_simp
    ring
  have hm : 0 ≤ 2 * y - (x - x ^ 2 / 2) := by rw [hdiff]; positivity
  rw [Real.norm_of_nonneg (by linarith)]
  have h₁ : x ^ 3 / (2 * (x + 2)) ≤ x ^ 3 / 4 := by
    gcongr
    linarith
  have h₂ : x ^ 3 / (4 * (x + 2) * (1 + x)) ≤ x ^ 3 / 8 := by
    gcongr
    nlinarith
  linarith

private noncomputable def logTwo (x : ℝ) : ℝ :=
  ∑' i : ℕ, Real.log (1 + (i : ℝ) * x) * (1 / 2 : ℝ) ^ i

private lemma logTwo_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun i : ℕ => Real.log (1 + (i : ℝ) * x) * (1 / 2 : ℝ) ^ i) ∧
    ‖logTwo x - (2 * x - 3 * x ^ 2)‖ ≤ (∑' i : ℕ, (i : ℝ) ^ 3 * (1 / 2 : ℝ) ^ i) * x ^ 3 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num [Real.norm_eq_abs]
  have h₁ : HasSum (fun i : ℕ => (i : ℝ) * (1 / 2 : ℝ) ^ i) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one hr using 1
    norm_num
  have h₂ : HasSum (fun i : ℕ => (i : ℝ) ^ 2 * (1 / 2 : ℝ) ^ i) 6 := by
    convert hasSum_sq_mul_geometric_of_norm_lt_one hr using 1
    norm_num
  let f (i : ℕ) := Real.log (1 + (i : ℝ) * x) * (1 / 2 : ℝ) ^ i
  let p (i : ℕ) := ((i : ℝ) * x - ((i : ℝ) * x) ^ 2 / 2) * (1 / 2 : ℝ) ^ i
  have hp : HasSum p (2 * x - 3 * x ^ 2) := by
    convert (h₁.mul_right x).sub (h₂.mul_right (x ^ 2 / 2)) using 1
    · funext i
      dsimp [p]
      ring
    · ring
  have hM := summable_pow_mul_geometric_of_norm_lt_one 3 hr
  have hbound (i : ℕ) : ‖f i - p i‖ ≤ (i : ℝ) ^ 3 * (1 / 2 : ℝ) ^ i * x ^ 3 := by
    dsimp only [f, p]
    rw [← sub_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ i),
      mul_right_comm, ← mul_pow]
    exact mul_le_mul_of_nonneg_right (log_quadratic_bound (by positivity)) (by positivity)
  have hs : Summable (fun i => ‖f i - p i‖) :=
    (hM.mul_right (x ^ 3)).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hf : Summable f := (hs.of_norm.add hp.summable).congr (fun i => sub_add_cancel (f i) (p i))
  refine ⟨hf, ?_⟩
  change ‖(∑' i, f i) - (2 * x - 3 * x ^ 2)‖ ≤ _
  rw [← hp.tsum_eq, ← hf.tsum_sub hp.summable, ← hM.tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hbound (hM.mul_right _))

private lemma exp_logTwo_quadratic :
    (fun x : ℝ => Real.exp (logTwo x) - (1 + 2 * x - x ^ 2))
      =O[𝓝[Set.Ici 0] 0] (fun x : ℝ => x ^ 3) := by
  let F : Filter ℝ := 𝓝[Set.Ici 0] 0
  have hle : F ≤ 𝓝 0 := nhdsWithin_le_nhds
  have h3 : (fun x : ℝ => logTwo x - (2 * x - 3 * x ^ 2)) =O[F] (fun x : ℝ => x ^ 3) := by
    refine IsBigO.of_bound (∑' i : ℕ, (i : ℝ) ^ 3 * (1 / 2 : ℝ) ^ i) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Real.norm_of_nonneg (pow_nonneg hx 3)] using (logTwo_quadratic hx).2
  have h32 : (fun x : ℝ => x ^ 3) =O[F] (fun x : ℝ => x ^ 2) :=
    ((isLittleO_pow_pow (by decide : 2 < 3)).isBigO).mono hle
  have h21 : (fun x : ℝ => x ^ 2) =O[F] (fun x : ℝ => x) :=
    (isLittleO_pow_id (by decide : 1 < 2)).isBigO.mono hle
  have h2 : (fun x : ℝ => logTwo x - 2 * x) =O[F] (fun x : ℝ => x ^ 2) := by
    refine ((h3.trans h32).add (isBigO_const_mul_self (-3 : ℝ) (fun x : ℝ => x ^ 2) F)).congr
      (fun x => ?_) (fun _ => rfl)
    ring
  have hx : (fun x : ℝ => 2 * x) =O[F] (fun x : ℝ => x) := isBigO_const_mul_self _ _ _
  have h : logTwo =O[F] (fun x : ℝ => x) :=
    ((h2.trans h21).add hx).congr (fun x => sub_add_cancel (logTwo x) (2 * x)) (fun _ => rfl)
  have hs : (fun x : ℝ => logTwo x ^ 2 - (2 * x) ^ 2) =O[F] (fun x : ℝ => x ^ 3) := by
    refine (h2.mul (h.add hx)).congr (fun x => ?_) (fun x => ?_)
    · ring
    · ring
  have ht := ((Real.exp_sub_sum_range_isBigO_pow 3).comp_tendsto (h.trans_tendsto hle)).trans
    (h.pow 3)
  have ht' : (fun x : ℝ => Real.exp (logTwo x) - (1 + logTwo x + logTwo x ^ 2 / 2))
      =O[F] (fun x : ℝ => x ^ 3) := by
    simpa [Function.comp_def, Finset.sum_range_succ] using ht
  refine ((ht'.add h3).add (hs.const_mul_left (1 / 2 : ℝ))).congr (fun x => ?_) (fun _ => rfl)
  ring

private noncomputable def expTwo (n : ℕ) : ℝ :=
  Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (2 : ℝ) ^ (m + 1))

private lemma expTwo_eq {n : ℕ} (hn : 0 < n) :
    expTwo n = n * Real.exp (logTwo (n : ℝ)⁻¹) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he (m : ℕ) : ((m + 1 : ℝ) + n) = n * (1 + (m + 1 : ℝ) * (n : ℝ)⁻¹) := by
    field_simp
    ring
  have hs : HasSum (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) 1 := by
    simpa only [pow_succ', one_div, div_eq_mul_inv, one_mul, inv_pow] using
      hasSum_geometric_two' (1 : ℝ)
  have ht := (logTwo_quadratic (show 0 ≤ (n : ℝ)⁻¹ by positivity)).1
  have hshift := (summable_nat_add_iff 1).mpr ht
  have hz : (∑' m : ℕ, Real.log (1 + ((m + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹) * (1 / 2 : ℝ) ^ (m + 1)) =
      logTwo (n : ℝ)⁻¹ := by
    unfold logTwo
    rw [ht.tsum_eq_zero_add]
    simp
  have hterm (m : ℕ) : Real.log ((m + 1 : ℝ) + n) / (2 : ℝ) ^ (m + 1) =
      Real.log n * (1 / 2 : ℝ) ^ (m + 1) +
        Real.log (1 + (m + 1 : ℝ) * (n : ℝ)⁻¹) * (1 / 2 : ℝ) ^ (m + 1) := by
    rw [he, Real.log_mul hn'.ne' (by positivity), div_eq_mul_inv, ← inv_pow, add_mul]
    simp only [one_div]
  simp only [expTwo, hterm]
  rw [(hs.summable.mul_left _).tsum_add (by simpa only [Nat.cast_add, Nat.cast_one] using hshift),
    hs.summable.tsum_mul_left, hs.tsum_eq, mul_one, Real.exp_add, Real.exp_log hn']
  rw [show (∑' m : ℕ, Real.log (1 + (m + 1 : ℝ) * (n : ℝ)⁻¹) * (1 / 2 : ℝ) ^ (m + 1)) =
    logTwo (n : ℝ)⁻¹ by simpa only [Nat.cast_add, Nat.cast_one] using hz]

private lemma expTwo_quadratic :
    (fun n : ℕ => expTwo n - ((n : ℝ) + 2 - (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[Set.Ici 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)),
      Eventually.of_forall (fun n => Set.mem_Ici.mpr (by positivity))⟩
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul
    (exp_logTwo_quadratic.comp_tendsto ht)
  refine h.congr' ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  · simp only [Function.comp_def, expTwo_eq hn]
    field_simp
  · simp only [Function.comp_def, inv_pow]
    field_simp

private def hasQuadraticExpansion (l : ℕ) : Prop :=
  ∃ C : ℝ, 1 < C ∧
    (fun n : ℕ => (gobelSequence 2 l n : ℝ) / C ^ (2 ^ n) - ((n : ℝ) + 2 - (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)

private lemma hasQuadraticExpansion_of_ge_two (l : ℕ) (hl : 2 ≤ l) : hasQuadraticExpansion l := by
  obtain ⟨C, hC, hlim⟩ := gobelSequence_root_tendsto_gt_one 2 l (by decide) hl
  refine ⟨C, hC, ?_⟩
  have herr : (fun n : ℕ => (gobelSequence 2 l n : ℝ) / C ^ (2 ^ n) - expTwo n)
      =O[atTop] (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    refine (gobelSequence_error_isBigO 2 l (by decide) hl C hlim 2 (by norm_num)).neg_left.congr'
      ?_ (Eventually.of_forall (fun n => ?_))
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hg : 0 ≤ (gobelSequence 2 l n : ℝ) := by
        simpa using somosLike_le_gobelSequence 2 l (by decide) hl (fun _ => 0) (by norm_num)
          (by norm_num) n hn
      have hr : ((gobelSequence 2 l n : ℝ) ^ ((2 : ℝ) ^ n)⁻¹) ^ (2 ^ n) = gobelSequence 2 l n := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          Real.rpow_inv_natCast_pow hg (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
      simp only [expTwo, neg_sub, div_pow, one_div, Nat.cast_ofNat, hr]
    · change (n : ℝ) ^ (-(2 : ℝ)) = _
      rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
  refine (herr.add expTwo_quadratic).congr (fun n => ?_) (fun _ => rfl)
  ring

-- Both initial values have the same coefficients 2 and -1. This calculation
-- does not use `gobelSequence_asymptotic_expansion` or any of its private lemmas.
example : hasQuadraticExpansion 2 ∧ hasQuadraticExpansion 3 :=
  ⟨hasQuadraticExpansion_of_ge_two 2 (by decide), hasQuadraticExpansion_of_ge_two 3 (by decide)⟩

-- Exercise the all-orders API at two initial values with one shared witness.
example : ∃ a : ℕ → ℝ, ∀ l ∈ ({2, 3} : Finset ℕ), ∃ C : ℝ, 1 < C ∧ ∀ R : ℕ,
    (fun n : ℕ => (gobelSequence 2 l n : ℝ) - C ^ (2 ^ n) * (n : ℝ) *
          (1 + ∑ r ∈ Finset.Icc 1 R, a r / (n : ℝ) ^ r))
      =O[atTop] (fun n : ℕ => C ^ (2 ^ n) * (n : ℝ) / (n : ℝ) ^ (R + 1)) := by
  obtain ⟨a, h⟩ := gobelSequence_asymptotic_expansion 2 (by decide)
  refine ⟨a, fun l hl => ?_⟩
  have hl' : 2 ≤ l := by
    simp only [mem_insert, mem_singleton] at hl
    rcases hl with rfl | rfl <;> decide
  norm_num at h
  exact h l hl'

end MetaMathlibExt
