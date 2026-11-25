/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import MathlibExt.NumberTheory.PrimeCounting.SquarefreeTotient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic

namespace MathlibExt.NumberTheory.PrimeCounting

open scoped BigOperators
open Finset MeasureTheory

private noncomputable def btWeightedPrefix (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 0 n, c k

private noncomputable def btSieveWeight (z : ℕ) (t : ℝ) : ℝ :=
  (z : ℝ) / (z + t)

private noncomputable def btSieveKernel (z : ℕ) (t : ℝ) : ℝ :=
  (z : ℝ) / (z + t) ^ 2

private theorem btSieveWeight_hasDerivAt (z : ℕ) (t : ℝ)
    (ht : -(z : ℝ) ≠ t) :
    HasDerivAt (btSieveWeight z) (-btSieveKernel z t) t := by
  have hne : (z : ℝ) + t ≠ 0 := by
    intro hzero
    apply ht
    linarith
  unfold btSieveWeight btSieveKernel
  convert (hasDerivAt_const t (z : ℝ)).div
    ((hasDerivAt_const t (z : ℝ)).add (hasDerivAt_id t)) hne using 1
  · rfl
  · simp only [Pi.add_apply, id_eq, zero_mul, zero_add]
    ring

private theorem btAbelDecomposition (c : ℕ → ℝ) (z : ℕ) (hc : c 0 = 0)
    (hz : 6 ≤ z) :
    (∑ q ∈ (Icc 1 z : Finset ℕ), btSieveWeight z (q : ℝ) * c q) =
      ∑ q ∈ (Icc 1 6 : Finset ℕ),
        (btSieveWeight z (q : ℝ) - btSieveWeight z 6) * c q +
        btSieveWeight z z * btWeightedPrefix c z +
          ∫ t in Set.Ioc (6 : ℝ) z,
            btSieveKernel z t * btWeightedPrefix c ⌊t⌋₊ := by
  have hzR : (6 : ℝ) ≤ z := by exact_mod_cast hz
  have hne (t : ℝ) (ht : t ∈ Set.Icc (6 : ℝ) z) : -(z : ℝ) ≠ t := by
    intro heq
    have htpos : 0 < t := by linarith [ht.1]
    have hznonneg : (0 : ℝ) ≤ z := by positivity
    linarith
  have hdiff : ∀ t ∈ Set.Icc (6 : ℝ) z,
      DifferentiableAt ℝ (btSieveWeight z) t := by
    intro t ht
    exact (btSieveWeight_hasDerivAt z t (hne t ht)).differentiableAt
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (6 : ℝ) z) :
      deriv (btSieveWeight z) t = -btSieveKernel z t :=
    (btSieveWeight_hasDerivAt z t (hne t ht)).deriv
  have hint : IntegrableOn (deriv (btSieveWeight z)) (Set.Icc (6 : ℝ) z) := by
    have hk : ContinuousOn (fun t : ℝ ↦ -btSieveKernel z t)
        (Set.Icc (6 : ℝ) z) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      have htpos : 0 < t := by linarith [ht.1]
      have hden : (z : ℝ) + t ≠ 0 := by positivity
      have hdenpow : ((z : ℝ) + t) ^ 2 ≠ 0 := pow_ne_zero 2 hden
      exact ((continuousAt_const.div
        ((continuousAt_const.add continuousAt_id).pow 2) hdenpow).neg)
    exact hk.integrableOn_Icc.congr_fun (fun t ht ↦ (hderiv t ht).symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul' c hz hdiff hint
  norm_num only [Nat.cast_ofNat] at habel
  have hsets : Icc 1 z = Icc 1 6 ∪ Ioc 6 z := by
    ext q
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 6) (Ioc 6 z) := by
    apply Finset.disjoint_left.mpr
    intro q hq1 hq2
    simp only [mem_Icc] at hq1
    simp only [mem_Ioc] at hq2
    omega
  have hsplit :
      (∑ q ∈ (Icc 1 z : Finset ℕ), btSieveWeight z (q : ℝ) * c q) =
        (∑ q ∈ (Icc 1 6 : Finset ℕ), btSieveWeight z (q : ℝ) * c q) +
          ∑ q ∈ (Ioc 6 z : Finset ℕ), btSieveWeight z (q : ℝ) * c q := by
    rw [hsets, Finset.sum_union hdisj]
  have hprefix : btWeightedPrefix c 6 = ∑ q ∈ Icc 1 6, c q := by
    rw [btWeightedPrefix]
    have hset : Icc 0 6 = {0} ∪ Icc 1 6 := by
      ext q
      simp only [mem_Icc, mem_union, mem_singleton]
      omega
    rw [hset, Finset.sum_union]
    · simp [hc]
    · exact Finset.disjoint_left.mpr (by simp)
  have hintegral :
      (∫ t in Set.Ioc (6 : ℝ) z,
        deriv (btSieveWeight z) t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -∫ t in Set.Ioc (6 : ℝ) z,
        btSieveKernel z t * btWeightedPrefix c ⌊t⌋₊ := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t htz
    change deriv (btSieveWeight z) t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -(btSieveKernel z t * btWeightedPrefix c ⌊t⌋₊)
    rw [hderiv t (Set.Ioc_subset_Icc_self htz)]
    simp only [btWeightedPrefix]
    ring
  rw [hsplit, habel, hintegral]
  simp only [sub_neg_eq_add]
  change (∑ q ∈ (Icc 1 6 : Finset ℕ), btSieveWeight z (q : ℝ) * c q) +
      (btSieveWeight z z * btWeightedPrefix c z -
        btSieveWeight z 6 * btWeightedPrefix c 6 +
          ∫ t in Set.Ioc (6 : ℝ) z,
            btSieveKernel z t * btWeightedPrefix c ⌊t⌋₊) = _
  rw [hprefix]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem btIntegralPrefixLower (c : ℕ → ℝ) (C : ℝ) (z : ℕ)
    (hz : 6 ≤ z)
    (hD : ∀ n : ℕ, 6 ≤ n → Real.log (n + 1) + C ≤ btWeightedPrefix c n) :
    (∫ t in Set.Ioc (6 : ℝ) z,
        btSieveKernel z t * (Real.log t + C)) ≤
      ∫ t in Set.Ioc (6 : ℝ) z,
        btSieveKernel z t * btWeightedPrefix c ⌊t⌋₊ := by
  have hzR : (6 : ℝ) ≤ z := by exact_mod_cast hz
  have hkerCont : ContinuousOn (btSieveKernel z) (Set.Icc (6 : ℝ) z) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have htpos : 0 < t := by linarith [ht.1]
    have hden : (z : ℝ) + t ≠ 0 := by positivity
    have hdenpow : ((z : ℝ) + t) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    exact continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2) hdenpow
  have hkerInt : IntegrableOn (btSieveKernel z) (Set.Icc (6 : ℝ) z) :=
    hkerCont.integrableOn_Icc
  have hleftCont :
      ContinuousOn (fun t : ℝ ↦ btSieveKernel z t * (Real.log t + C))
        (Set.Icc (6 : ℝ) z) := by
    apply hkerCont.mul
    exact ((Real.continuousOn_log.mono (by
      intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      simpa using htpos.ne')).add continuousOn_const)
  have hleftInt :
      IntegrableOn (fun t : ℝ ↦ btSieveKernel z t * (Real.log t + C))
        (Set.Ioc (6 : ℝ) z) :=
    hleftCont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hrightInt :
      IntegrableOn (fun t : ℝ ↦ btSieveKernel z t * btWeightedPrefix c ⌊t⌋₊)
        (Set.Ioc (6 : ℝ) z) := by
    exact (integrableOn_mul_sum_Icc c (by norm_num : (0 : ℝ) ≤ 6) hkerInt).mono_set
      Set.Ioc_subset_Icc_self
  apply MeasureTheory.setIntegral_mono_on hleftInt hrightInt measurableSet_Ioc
  intro t ht
  have htpos : 0 < t := by linarith [ht.1]
  have hfloor : 6 ≤ ⌊t⌋₊ := Nat.le_floor ht.1.le
  have hlog : Real.log t ≤ Real.log (⌊t⌋₊ + 1) := by
    apply Real.log_le_log htpos
    exact (Nat.lt_floor_add_one t).le
  have hprefix : Real.log t + C ≤ btWeightedPrefix c ⌊t⌋₊ := by
    linarith [hlog, hD ⌊t⌋₊ hfloor]
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hker : (0 : ℝ) ≤ btSieveKernel z t := by
    rw [btSieveKernel]
    positivity
  exact mul_le_mul_of_nonneg_left hprefix hker

private noncomputable def btSieveAntiderivative (z : ℕ) (C t : ℝ) : ℝ :=
  -btSieveWeight z t * (Real.log t + C) + Real.log t - Real.log (z + t)

private theorem btSieveAntiderivative_hasDerivAt (z : ℕ) (C t : ℝ)
    (ht : 0 < t) :
    HasDerivAt (btSieveAntiderivative z C)
      (btSieveKernel z t * (Real.log t + C)) t := by
  have hzsum : (z : ℝ) + t ≠ 0 := by positivity
  have hweight := btSieveWeight_hasDerivAt z t (by intro heq; linarith)
  have hlog := Real.hasDerivAt_log ht.ne'
  have hsum := (hasDerivAt_const t (z : ℝ)).add (hasDerivAt_id t)
  have hlogsum := (Real.hasDerivAt_log hzsum).comp t hsum
  unfold btSieveAntiderivative
  convert ((hweight.neg.mul (hlog.add_const C)).add hlog).sub hlogsum using 1
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
      Function.comp_apply]
  · simp only [neg_neg, Pi.neg_apply, neg_mul, zero_add, mul_one]
    unfold btSieveWeight btSieveKernel
    field_simp
    ring

private theorem btIntegralKernelLog_eq (C : ℝ) (z : ℕ) (hz : 6 ≤ z) :
    (∫ t in Set.Ioc (6 : ℝ) z,
        btSieveKernel z t * (Real.log t + C)) =
      btSieveAntiderivative z C z - btSieveAntiderivative z C 6 := by
  have hzR : (6 : ℝ) ≤ z := by exact_mod_cast hz
  rw [← intervalIntegral.integral_of_le hzR]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzR
  · intro t ht
    exact (btSieveAntiderivative_hasDerivAt z C t
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    exact btSieveAntiderivative_hasDerivAt z C t (by linarith [ht.1])
  · have hcont :
        ContinuousOn (fun t : ℝ ↦ btSieveKernel z t * (Real.log t + C))
          (Set.Icc (6 : ℝ) z) := by
      intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.mul
      · unfold btSieveKernel
        have hden : (z : ℝ) + t ≠ 0 := by positivity
        exact continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2)
          (pow_ne_zero 2 hden)
      · exact (Real.continuousAt_log htpos.ne').add continuousAt_const
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hzR]
    exact hcont.integrableOn_Icc

private theorem btCorrectionLower (c : ℕ → ℝ) (z : ℕ) (hz : 100 ≤ z)
    (h1 : c 1 = 1) (h2 : c 2 = 1) (h3 : c 3 = 1 / 2)
    (h4 : c 4 = 0) (h5 : c 5 = 1 / 4) :
    (967 / 100 : ℝ) / (z + 6) <
      ∑ q ∈ (Icc 1 6 : Finset ℕ),
        (btSieveWeight z (q : ℝ) - btSieveWeight z 6) * c q := by
  rw [show (Icc 1 6 : Finset ℕ) = {1, 2, 3, 4, 5, 6} by decide]
  norm_num [h1, h2, h3, h4, h5, btSieveWeight]
  have hzR : (100 : ℝ) ≤ z := by exact_mod_cast hz
  field_simp
  ring_nf at *
  have hy : (0 : ℝ) ≤ z - 100 := by linarith
  have hpoly : (0 : ℝ) <
      79904938320 + 3271434104 * (z - 100) + 50094224 * (z - 100) ^ 2 +
        340104 * (z - 100) ^ 3 + 864 * (z - 100) ^ 4 := by positivity
  nlinarith [hpoly]

private theorem btLogOneAddLower (z : ℕ) (hz : 0 < z) :
    (6 : ℝ) / (z + 6) < Real.log (1 + 6 / z) := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  let x : ℝ := 1 + 6 / z
  have hxpos : 0 < x := by simp only [x]; positivity
  have hxne : x ≠ 1 := by
    simp only [x]
    have hdiv : (0 : ℝ) < 6 / z := by positivity
    linarith
  have hlog := Real.self_sub_one_lt_mul_log hxpos.le hxne
  apply lt_of_mul_lt_mul_left ?_ hxpos.le
  calc
    x * (6 / ((z : ℝ) + 6)) = x - 1 := by
      simp only [x]
      field_simp
      ring
    _ < x * Real.log x := hlog
    _ = x * Real.log (1 + 6 / z) := by rfl

private theorem btEndpointLower (C : ℝ) (z : ℕ) (hz : 0 < z) :
    Real.log z + C - Real.log 2 +
        (6 - 6 * (Real.log 6 + C)) / (z + 6) <
      (1 / 2 : ℝ) * (Real.log z + C) +
        (btSieveAntiderivative z C z - btSieveAntiderivative z C 6) := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hzz : Real.log ((z : ℝ) + z) = Real.log z + Real.log 2 := by
    calc
      Real.log ((z : ℝ) + z) = Real.log ((z : ℝ) * 2) := by congr 1; ring
      _ = _ := Real.log_mul hzR.ne' (by norm_num)
  have hplus : Real.log ((z : ℝ) + 6) =
      Real.log z + Real.log (1 + 6 / z) := by
    calc
      Real.log ((z : ℝ) + 6) = Real.log ((z : ℝ) * (1 + 6 / z)) := by
        congr 1
        field_simp
      _ = _ := Real.log_mul hzR.ne' (by positivity)
  have hhalf : (z : ℝ) / (z + z) = 1 / 2 := by field_simp; ring
  have hratio : (z : ℝ) / (z + 6) = 1 - 6 / (z + 6) := by field_simp; ring
  have hlog := btLogOneAddLower z hz
  unfold btSieveAntiderivative btSieveWeight
  rw [hzz, hplus, hhalf, hratio]
  ring_nf at hlog ⊢
  linarith

private theorem btFinalConstant (z : ℕ) (hz : 100 ≤ z) :
    (36 / 100 : ℝ) < 107 / 100 - Real.log 2 +
      (1567 / 100 - 6 * (Real.log 6 + 107 / 100)) / (z + 6) := by
  let B : ℝ := 1567 / 100 -
    6 * (0.6931471808 + 1.0986122888 + 107 / 100)
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have hB : B ≤ 1567 / 100 - 6 * (Real.log 6 + 107 / 100) := by
    rw [hlog6]
    dsimp only [B]
    linarith
  have hBneg : B < 0 := by
    dsimp only [B]
    norm_num
  have hzR : (100 : ℝ) ≤ z := by exact_mod_cast hz
  have hden : (106 : ℝ) ≤ z + 6 := by linarith
  have hBfrac : B / 106 ≤ B / ((z : ℝ) + 6) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 106) (by positivity)).mpr
    nlinarith
  have hfrac : B / 106 ≤
      (1567 / 100 - 6 * (Real.log 6 + 107 / 100)) / ((z : ℝ) + 6) := by
    exact hBfrac.trans (div_le_div_of_nonneg_right hB (by positivity))
  have hnum : (36 / 100 : ℝ) < 107 / 100 - 0.6931471808 + B / 106 := by
    dsimp only [B]
    norm_num
  linarith

private theorem btWeightedPrefixLower (c : ℕ → ℝ) (z : ℕ) (hc : c 0 = 0)
    (hz : 100 ≤ z)
    (hD : ∀ n : ℕ, 6 ≤ n → Real.log (n + 1) + 107 / 100 < btWeightedPrefix c n)
    (h1 : c 1 = 1) (h2 : c 2 = 1) (h3 : c 3 = 1 / 2)
    (h4 : c 4 = 0) (h5 : c 5 = 1 / 4) :
    Real.log z + 36 / 100 <
      ∑ q ∈ (Icc 1 z : Finset ℕ), btSieveWeight z (q : ℝ) * c q := by
  have hz6 : 6 ≤ z := hz.trans' (by norm_num)
  rw [btAbelDecomposition c z hc hz6]
  have hcorr := btCorrectionLower c z hz h1 h2 h3 h4 h5
  have hzpos : 0 < z := by omega
  have hzR : (0 : ℝ) < z := by exact_mod_cast hzpos
  have hlogz : Real.log z < Real.log (z + 1) := by
    apply Real.strictMonoOn_log
    · exact hzR
    · change (0 : ℝ) < z + 1
      positivity
    · exact_mod_cast Nat.lt_succ_self z
  have hprefix : Real.log z + 107 / 100 < btWeightedPrefix c z := by
    linarith [hD z hz6]
  have hwtzz : btSieveWeight z z = (1 / 2 : ℝ) := by
    rw [btSieveWeight]
    field_simp
    ring
  have hend : (1 / 2 : ℝ) * (Real.log z + 107 / 100) <
      btSieveWeight z z * btWeightedPrefix c z := by
    rw [hwtzz]
    nlinarith
  have hint := btIntegralPrefixLower c (107 / 100) z hz6
    (fun n hn ↦ (hD n hn).le)
  rw [btIntegralKernelLog_eq (107 / 100) z hz6] at hint
  have hendpoint := btEndpointLower (107 / 100) z hzpos
  have hconst := btFinalConstant z hz
  have hfracid : (967 / 100 : ℝ) / (z + 6) +
      (6 - 6 * (Real.log 6 + 107 / 100)) / (z + 6) =
      (1567 / 100 - 6 * (Real.log 6 + 107 / 100)) / (z + 6) := by
    ring
  linarith

private noncomputable def btMoebiusTotientTerm (q : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q)

private theorem btMoebiusTotientTerm_zero : btMoebiusTotientTerm 0 = 0 := by
  norm_num [btMoebiusTotientTerm, ArithmeticFunction.moebius]

private theorem btWeightedPrefix_eq_moebiusSum (z : ℕ) :
    btWeightedPrefix btMoebiusTotientTerm z =
      ∑ q ∈ Icc 1 z, btMoebiusTotientTerm q := by
  rw [btWeightedPrefix]
  have hset : Icc 0 z = {0} ∪ Icc 1 z := by
    ext q
    simp only [mem_Icc, mem_union, mem_singleton]
    omega
  rw [hset, Finset.sum_union]
  · simp [btMoebiusTotientTerm_zero]
  · exact Finset.disjoint_left.mpr (by simp)

private theorem btMoebiusTotientTerm_one : btMoebiusTotientTerm 1 = 1 := by
  norm_num [btMoebiusTotientTerm, ArithmeticFunction.moebius]

private theorem btMoebiusTotientTerm_two : btMoebiusTotientTerm 2 = 1 := by
  rw [btMoebiusTotientTerm,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    Nat.totient_prime Nat.prime_two]
  norm_num

private theorem btMoebiusTotientTerm_three : btMoebiusTotientTerm 3 = 1 / 2 := by
  rw [btMoebiusTotientTerm,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    Nat.totient_prime Nat.prime_three]
  norm_num

private theorem btMoebiusTotientTerm_four : btMoebiusTotientTerm 4 = 0 := by
  have h4 : ¬Squarefree 4 := by
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) (by norm_num)
  rw [btMoebiusTotientTerm,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree h4]
  norm_num

private theorem btMoebiusTotientTerm_five : btMoebiusTotientTerm 5 = 1 / 4 := by
  have h5 : Nat.Prime 5 := by norm_num
  rw [btMoebiusTotientTerm, ArithmeticFunction.moebius_apply_prime h5,
    Nat.totient_prime h5]
  norm_num

private theorem btSieveWeight_eq (z q : ℕ) (hz : 0 < z) :
    btSieveWeight z q = (1 + (q : ℝ) / z)⁻¹ := by
  rw [btSieveWeight]
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  field_simp

/--
**Weighted lower bound for the squarefree totient sum.** For every natural number $z \ge 100$,
$\log z + 36/100 < \sum_{q=1}^{z} (1 + q/z)^{-1} \, \mu(q)^2 / \varphi(q)$, where $\mu$ is the
Möbius function and $\varphi$ is Euler's totient function.

Source: Montgomery–Vaughan, *The large sieve* (1973), Lemma 8, lines
658–714. The proof uses Abel summation, `moebiusSq_div_totient_sum_gt_log`,
and the paper's explicit correction from the terms `q ≤ 5`.
-/
public theorem squarefreeTotientWeightedLower (z : ℕ) (hz : 100 ≤ z) :
    Real.log z + 36 / 100 <
      ∑ q ∈ Finset.Icc 1 z, (1 + (q : ℝ) / z)⁻¹ *
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q) := by
  have hD (n : ℕ) (hn : 6 ≤ n) :
      Real.log (n + 1) + 107 / 100 <
        btWeightedPrefix btMoebiusTotientTerm n := by
    rw [btWeightedPrefix_eq_moebiusSum]
    exact moebiusSq_div_totient_sum_gt_log n hn
  have hmain := btWeightedPrefixLower btMoebiusTotientTerm z
    btMoebiusTotientTerm_zero hz hD btMoebiusTotientTerm_one
    btMoebiusTotientTerm_two btMoebiusTotientTerm_three
    btMoebiusTotientTerm_four btMoebiusTotientTerm_five
  calc
    Real.log z + 36 / 100 <
        ∑ q ∈ (Icc 1 z : Finset ℕ),
          btSieveWeight z (q : ℝ) * btMoebiusTotientTerm q := hmain
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [btSieveWeight_eq z q (by omega : 0 < z)]
      rfl

end MathlibExt.NumberTheory.PrimeCounting
