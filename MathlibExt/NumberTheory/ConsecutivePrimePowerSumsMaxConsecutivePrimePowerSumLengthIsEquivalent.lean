/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The nth-prime asymptotic argument is adapted from
`MathlibExt/NumberTheory/PrimeCounting/PrimePrimeRatio.lean` in `facebookresearch/atlas-lean`,
revision `23d85f13aa5470466339c40e7dc0a9f142c4737d`.
Copyright (c) Meta Platforms, Inc. and affiliates.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source file does not name individual authors.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Length of the longest sum of consecutive prime powers

The maximum length of an initial sum of prime powers is asymptotic to
`(k + 1) * x ^ (1 / (k + 1)) / (Real.log x) ^ (k / (k + 1))` for `1 < k`.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Lemma 2
(`integers-2024-A4-lem-2`).
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset
open scoped Topology

private theorem nth_prime_asymptotic :
    (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log n) := by
  let p := fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)
  have hp : Tendsto p atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hcount : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] (fun n => p n / Real.log (p n)) := by
    simpa only [p, Function.comp_def, Nat.floor_natCast, Nat.primeCounting,
      Nat.primeCounting', Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime,
      Nat.cast_add_one] using
      Nat.isEquivalent_primeCounting.comp_tendsto hp
  have hlog : (fun x : ℝ => Real.log (x / Real.log x)) ~[atTop] Real.log := by
    have h := IsEquivalent.refl.sub_isLittleO
      (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop)
    refine h.congr_left ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp only [Pi.sub_apply, Function.comp_apply, id_eq,
      Real.log_div (by linarith : x ≠ 0) (Real.log_pos hx).ne']
  have hn : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)
  have hlp : (fun n => Real.log (p n)) ~[atTop] (fun n : ℕ => Real.log n) :=
    (hlog.comp_tendsto hp).symm.trans
      ((hcount.symm.log (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).trans
        (hn.log tendsto_natCast_atTop_atTop))
  have h := (hcount.symm.trans hn).mul hlp
  refine h.congr_left ?_
  filter_upwards [hp.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
  simp only [Pi.mul_apply]
  exact div_mul_cancel₀ _ (Real.log_pos hn).ne'

private noncomputable def modelSum (k : ℕ) (x : ℝ) : ℝ :=
  x ^ (k + 1) * Real.log x ^ k / (k + 1)

private theorem modelSum_deriv (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (modelSum k)
      ((x * Real.log x) ^ k * (1 + (k : ℝ) / ((k + 1) * Real.log x))) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h := (((hasDerivAt_id x).pow (k + 1)).mul
    ((Real.hasDerivAt_log hx0).pow k)).div_const ((k : ℝ) + 1)
  change HasDerivAt (fun y : ℝ => y ^ (k + 1) * Real.log y ^ k / ((k : ℝ) + 1)) _ x
  convert h using 1
  · rfl
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one,
      Pi.pow_apply, id_eq]
    rw [mul_pow]
    have he : Real.log x ^ k = Real.log x ^ (k - 1) * Real.log x := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [he, pow_succ x]
    field_simp

private theorem modelSum_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (modelSum k) atTop atTop := by
  have hpow (j : ℕ) (hj : 0 < j) : Tendsto (fun x : ℝ => x ^ j) atTop atTop := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_atTop (by exact_mod_cast hj : (0 : ℝ) < j)
  exact ((hpow (k + 1) (by omega)).atTop_mul_atTop₀
    ((hpow k hk).comp Real.tendsto_log_atTop)).atTop_div_const
      (by positivity : (0 : ℝ) < (k : ℝ) + 1)

private theorem modelSum_mean_value (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ∃ c : ℝ, (n : ℝ) + 2 < c ∧ c < n + 3 ∧
    modelSum k (n + 3) - modelSum k (n + 2) =
      (c * Real.log c) ^ k * (1 + (k : ℝ) / ((k + 1) * Real.log c)) := by
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope (modelSum k)
    (fun x => (x * Real.log x) ^ k * (1 + (k : ℝ) / ((k + 1) * Real.log x)))
    (by linarith : (n : ℝ) + 2 < n + 3)
    (fun x hx => (modelSum_deriv k hk x
      (by
        have := hx.1
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)).continuousAt.continuousWithinAt)
    (fun x hx => modelSum_deriv k hk x
      (by have := hx.1; have := Nat.cast_nonneg (α := ℝ) n; linarith))
  refine ⟨c, hc.1, hc.2, ?_⟩
  simpa only [add_sub_add_left_eq_sub, show (3 : ℝ) - 2 = 1 by norm_num, div_one] using he.symm

private theorem modelSum_increment (k : ℕ) (hk : 0 < k) :
    (fun n : ℕ => modelSum k (n + 3) - modelSum k (n + 2)) ~[atTop]
      (fun n : ℕ => ((n : ℝ) * Real.log n) ^ k) := by
  choose c hc1 hc2 he using modelSum_mean_value k hk
  have hctop : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun n => (hc1 n).le)
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hcn : c ~[atTop] (fun n : ℕ => (n : ℝ)) := by
    apply isEquivalent_of_tendsto_one
    change Tendsto (fun n : ℕ => c n / n) atTop (𝓝 1)
    have hratio (a : ℝ) : Tendsto (fun n : ℕ => ((n : ℝ) + a) / n) atTop (𝓝 1) := by
      have h : Tendsto (fun n : ℕ => 1 + a / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
        simpa using tendsto_const_nhds.add
          (tendsto_natCast_atTop_atTop.const_div_atTop a)
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      simp [div_eq_mul_inv, add_mul, (by positivity : (n : ℝ) ≠ 0)]
    have hlow := hratio 2
    have hupp := hratio 3
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact div_le_div_of_nonneg_right (hc1 n).le (Nat.cast_nonneg n)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact div_le_div_of_nonneg_right (hc2 n).le (Nat.cast_nonneg n)
  have hfactor : Tendsto (fun n => 1 + (k : ℝ) / ((k + 1) * Real.log (c n)))
      atTop (𝓝 1) := by
    simpa using (((Real.tendsto_log_atTop.comp hctop).const_mul_atTop
      (by positivity : (0 : ℝ) < (k : ℝ) + 1)).const_div_atTop (k : ℝ)).const_add 1
  have hpow := (hcn.mul (hcn.log tendsto_natCast_atTop_atTop)).pow k
  have h := hpow.mul ((isEquivalent_const_iff_tendsto (by norm_num : (1 : ℝ) ≠ 0)).mpr hfactor)
  exact (h.congr_left (Eventually.of_forall (fun n => (he n).symm))).congr_right
    (Eventually.of_forall (fun n => mul_one _))

private theorem modelSum_shift (k : ℕ) (a : ℝ) :
    (fun n : ℕ => modelSum k (n + a)) ~[atTop] (fun n : ℕ => modelSum k n) := by
  have h : (fun n : ℕ => (n : ℝ) + a) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)
  exact ((h.pow (k + 1)).mul ((h.log tendsto_natCast_atTop_atTop).pow k)).div
    (IsEquivalent.refl (u := fun _ => (k : ℝ) + 1))

private theorem prime_sum_asymptotic (k : ℕ) (hk : 0 < k) :
    (fun n : ℕ => ((∑ i ∈ range n, Nat.nth Nat.Prime i ^ k : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => modelSum k n) := by
  let f : ℕ → ℝ := fun n => modelSum k (n + 2)
  let g : ℕ → ℝ := fun n => f (n + 1) - f n
  have hg : (fun n : ℕ => g n) ~[atTop]
      (fun n : ℕ => ((n : ℝ) * Real.log n) ^ k) := by
    simpa only [g, f, Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 2 = 3 by norm_num] using modelSum_increment k hk
  have hpg : (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) ^ k) ~[atTop] g :=
    (nth_prime_asymptotic.pow k).trans hg.symm
  have hgpos (n : ℕ) : 0 ≤ g n := by
    obtain ⟨c, hc, _, he⟩ := modelSum_mean_value k hk n
    have hc1 : 1 < c := by have := Nat.cast_nonneg (α := ℝ) n; linarith [hc]
    have hpos : 0 < (c * Real.log c) ^ k * (1 + (k : ℝ) / ((k + 1) * Real.log c)) := by
      have := Real.log_pos hc1
      have := Nat.cast_pos (α := ℝ).mpr hk
      positivity
    simpa only [g, f, Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 2 = 3 by norm_num] using he.symm ▸ hpos.le
  have htel (n : ℕ) : ∑ i ∈ range n, g i = f n - f 0 := sum_range_sub f n
  have hftop : Tendsto f atTop atTop := (modelSum_tendsto k hk).comp
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hgtop : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop := by
    simpa only [htel, sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-f 0) hftop
  have hsum : (fun n => ∑ i ∈ range n, (Nat.nth Nat.Prime i : ℝ) ^ k) ~[atTop]
      (fun n => ∑ i ∈ range n, g i) := by
    simpa only [IsEquivalent, Pi.sub_def, sum_sub_distrib] using
      hpg.isLittleO.sum_range hgpos hgtop
  have hsub : (fun n => ∑ i ∈ range n, g i) ~[atTop] f := by
    simpa only [htel, sub_eq_add_neg] using IsEquivalent.refl.add_const_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp hftop) (c := -f 0)
  simpa only [Nat.cast_sum, Nat.cast_pow] using
    (hsum.trans hsub).trans (modelSum_shift k 2)

private noncomputable def primeSum (k n : ℕ) : ℕ := ∑ i ∈ range n, Nat.nth Nat.Prime i ^ k

private noncomputable def maxLength (k x : ℕ) : ℕ := Nat.findGreatest (fun m => primeSum k m ≤ x) x

private theorem primeSum_ge (k n : ℕ) : n ≤ primeSum k n := by
  calc
    n = ∑ i ∈ range n, (1 : ℕ) := by simp
    _ ≤ primeSum k n := sum_le_sum fun i _ =>
      Nat.one_le_pow k _ (Nat.prime_nth_prime i).pos

private theorem maxLength_bounds (k x : ℕ) :
    primeSum k (maxLength k x) ≤ x ∧ x < primeSum k (maxLength k x + 1) := by
  constructor
  · change primeSum k (Nat.findGreatest (fun m => primeSum k m ≤ x) x) ≤ x
    apply Nat.findGreatest_spec (P := fun m => primeSum k m ≤ x) (m := 0) (Nat.zero_le x)
    simp [primeSum]
  · by_cases h : maxLength k x + 1 ≤ x
    · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun m => primeSum k m ≤ x)
        (n := x) (Nat.lt_succ_self (maxLength k x)) h)
    · exact (lt_of_not_ge h).trans_le (primeSum_ge k _)

private theorem maxLength_tendsto (k : ℕ) : Tendsto (maxLength k) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (max n (primeSum k n))] with x hx
  exact Nat.le_findGreatest ((le_max_left _ _).trans hx) ((le_max_right _ _).trans hx)

private theorem inverse_asymptotic (k : ℕ) (hk : 0 < k) :
    (fun x : ℕ => (x : ℝ)) ~[atTop] (fun x => modelSum k (maxLength k x)) := by
  have hm := maxLength_tendsto k
  have hf := (modelSum_tendsto k hk).comp (tendsto_natCast_atTop_atTop.comp hm)
  have hlo : (fun x => (primeSum k (maxLength k x) : ℝ)) ~[atTop]
      (fun x => modelSum k (maxLength k x)) := by
    simpa only [primeSum, Function.comp_def] using (prime_sum_asymptotic k hk).comp_tendsto hm
  have hhi : (fun x : ℕ => (primeSum k (maxLength k x + 1) : ℝ)) ~[atTop]
      (fun x => modelSum k (maxLength k x)) := by
    have hs := (prime_sum_asymptotic k hk).comp_tendsto ((tendsto_add_atTop_nat 1).comp hm)
    have hshift := (modelSum_shift k 1).comp_tendsto hm
    have hs' : (fun x => (primeSum k (maxLength k x + 1) : ℝ)) ~[atTop]
        (fun x => modelSum k ((maxLength k x : ℝ) + 1)) := by
      simpa only [primeSum, Function.comp_def, Nat.cast_add, Nat.cast_one] using hs
    exact hs'.trans hshift
  have hne := hf.eventually_ne_atTop 0
  apply isEquivalent_of_tendsto_one
  change Tendsto (fun x : ℕ => (x : ℝ) / modelSum k (maxLength k x)) atTop (𝓝 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((isEquivalent_iff_tendsto_one hne).mp hlo)
    ((isEquivalent_iff_tendsto_one hne).mp hhi)
  · filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    apply div_le_div_of_nonneg_right _ hx.le
    change (primeSum k (maxLength k x) : ℝ) ≤ x
    exact_mod_cast (maxLength_bounds k x).1
  · filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    apply div_le_div_of_nonneg_right _ hx.le
    change (x : ℝ) ≤ primeSum k (maxLength k x + 1)
    exact_mod_cast (maxLength_bounds k x).2.le

private theorem log_modelSum (k : ℕ) :
    (fun n : ℕ => Real.log (modelSum k n)) ~[atTop]
      (fun n : ℕ => ((k : ℝ) + 1) * Real.log n) := by
  have hlog := Real.isLittleO_log_id_atTop.comp_tendsto
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using hlog.tendsto_div_nhds_zero
  have hlim : Tendsto (fun n : ℕ => 1 + (k : ℝ) / (k + 1) *
      (Real.log (Real.log n) / Real.log n) -
      Real.log (k + 1) / (k + 1) / Real.log n) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hsmall)).sub
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop
        (Real.log (k + 1) / (k + 1)))
  apply isEquivalent_of_tendsto_one
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hl0 : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [Pi.div_apply, modelSum, Real.log_div (mul_ne_zero (pow_ne_zero _ hn0)
    (pow_ne_zero _ hl0)) hk0, Real.log_mul (pow_ne_zero _ hn0) (pow_ne_zero _ hl0),
    Real.log_pow, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem modelSum_root_identity (k n : ℕ) (hn : 1 < n) :
    ((k : ℝ) + 1) * modelSum k n ^ ((1 : ℝ) / (k + 1)) /
      (((k : ℝ) + 1) * Real.log n) ^ ((k : ℝ) / (k + 1)) = n := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hl0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hd0 : 0 < (k : ℝ) + 1 := by positivity
  have he1 : (((k + 1 : ℕ) : ℝ)) * ((1 : ℝ) / (k + 1)) = 1 := by
    push_cast
    field_simp
  have he2 : (k : ℝ) * ((1 : ℝ) / (k + 1)) = (k : ℝ) / (k + 1) := by ring
  have he3 : (1 : ℝ) / (k + 1) + (k : ℝ) / (k + 1) = 1 := by
    field_simp
    ring
  rw [modelSum, Real.div_rpow (by positivity) hd0.le,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul hn0.le, ← Real.rpow_natCast_mul hl0.le,
    he1, Real.rpow_one, he2, Real.mul_rpow hd0.le hl0.le]
  have hdpow : ((k : ℝ) + 1) ^ ((1 : ℝ) / (k + 1)) *
      ((k : ℝ) + 1) ^ ((k : ℝ) / (k + 1)) = (k : ℝ) + 1 := by
    rw [← Real.rpow_add hd0, he3, Real.rpow_one]
  have hlpow := (Real.rpow_pos_of_pos hl0 ((k : ℝ) / (k + 1))).ne'
  have hdapow := (Real.rpow_pos_of_pos hd0 ((1 : ℝ) / (k + 1))).ne'
  have hdbpow := (Real.rpow_pos_of_pos hd0 ((k : ℝ) / (k + 1))).ne'
  field_simp
  linear_combination -hdpow

private theorem finish_asymptotic (k : ℕ) (hk : 0 < k) :
    (fun x : ℕ =>
      (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ k ≤ x) x : ℝ)) ~[atTop]
      (fun x : ℕ => (k + 1) * (x : ℝ) ^ ((1 : ℝ) / (k + 1)) /
        Real.log x ^ ((k : ℝ) / (k + 1))) := by
  change (fun x : ℕ => (maxLength k x : ℝ)) ~[atTop]
    (fun x : ℕ => (k + 1) * (x : ℝ) ^ ((1 : ℝ) / (k + 1)) /
      Real.log x ^ ((k : ℝ) / (k + 1)))
  have hm := maxLength_tendsto k
  have hf := (modelSum_tendsto k hk).comp (tendsto_natCast_atTop_atTop.comp hm)
  have hx := inverse_asymptotic k hk
  have hlog : (fun x : ℕ => Real.log x) ~[atTop]
      (fun x => ((k : ℝ) + 1) * Real.log (maxLength k x)) :=
    (hx.log hf).trans ((log_modelSum k).comp_tendsto hm)
  have hfnn (x : ℕ) : 0 ≤ modelSum k (maxLength k x) := by
    unfold modelSum
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (pow_nonneg (Real.log_natCast_nonneg _) _)) (by positivity)
  have hlnn (x : ℕ) : 0 ≤ ((k : ℝ) + 1) * Real.log (maxLength k x) :=
    mul_nonneg (by positivity) (Real.log_natCast_nonneg _)
  have hroot := hx.rpow hfnn (r := (1 : ℝ) / (k + 1))
  have hlogroot := hlog.rpow hlnn (r := (k : ℝ) / (k + 1))
  have h := (IsEquivalent.refl (u := fun _ : ℕ => (k : ℝ) + 1)).mul (hroot.div hlogroot)
  refine (h.symm.congr_left ?_).congr_right ?_
  · filter_upwards [hm.eventually (eventually_gt_atTop (1 : ℕ))] with x hx
    simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    rw [← mul_div_assoc]
    exact modelSum_root_identity k _ hx
  · filter_upwards with x
    simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring

@[expose] public section

/-- **Length of the longest sum of consecutive prime powers.** Let $p_1 < p_2 < \cdots$ be the
primes, let $k > 1$ be a natural number, and for a natural number $x$ let $M(x, k)$ be the
largest $m \le x$ with $p_1^k + p_2^k + \cdots + p_m^k \le x$. Then
$M(x, k) \sim (k + 1)\, x^{1/(k+1)} / (\log x)^{k/(k+1)}$ (asymptotic equivalence) as $x \to \infty$
through the natural numbers.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Lemma 2
(`integers-2024-A4-lem-2`). -/
public theorem maxConsecutivePrimePowerSumLength_isEquivalent (k : ℕ) (hk : 1 < k) :
    (fun x : ℕ =>
        (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ k ≤ x) x : ℝ)) ~[atTop]
      fun x : ℕ => (k + 1) * (x : ℝ) ^ ((1 : ℝ) / (k + 1)) /
        Real.log x ^ ((k : ℝ) / (k + 1))
    := by
  exact finish_asymptotic k (Nat.zero_lt_of_lt hk)

end

end MetaMathlibExt
