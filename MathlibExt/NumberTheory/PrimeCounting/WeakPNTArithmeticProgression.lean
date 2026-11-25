/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.SumCoeff
import MathlibExt.Analysis.Asymptotics.MonotoneIntegralCriterion
import MathlibExt.Analysis.LaplaceTransform.Basic
import MathlibExt.Analysis.LaplaceTransform.ExponentialBound
import MathlibExt.Analysis.LaplaceTransform.NewmanTauberian
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi

open Filter MeasureTheory Set Topology
open scoped Asymptotics

namespace Chebyshev

/-- Nonnegativity of the residue-class psi function. -/
private lemma wpa_psiResidueClass_nonneg {q : ℕ} (b : ZMod q) (x : ℝ) :
    0 ≤ psiResidueClass b x := by
  unfold psiResidueClass
  exact Finset.sum_nonneg fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_nonneg b n

/-- The residue-class psi function is bounded by the full psi function. -/
private lemma wpa_psiResidueClass_le_psi {q : ℕ} (b : ZMod q) (x : ℝ) :
    psiResidueClass b x ≤ psi x := by
  simp only [psiResidueClass, psi]
  exact Finset.sum_le_sum fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_le b n

/-- Monotonicity of the residue-class psi function. -/
private lemma wpa_psiResidueClass_mono {q : ℕ} (b : ZMod q) :
    Monotone (psiResidueClass b) := by
  intro x y hxy
  simp only [psiResidueClass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc (by rfl) (by gcongr)
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt.residueClass_nonneg b n

/-- Linear upper bound for the residue-class psi function. -/
private lemma wpa_psiResidueClass_le_mul_self {q : ℕ} (b : ZMod q) {x : ℝ}
    (hx : 0 ≤ x) :
    psiResidueClass b x ≤ (Real.log 4 + 4) * x :=
  le_trans (wpa_psiResidueClass_le_psi b x) (psi_le_const_mul_self hx)

/-- The residue-class psi function at a natural number is a sum over `Icc 1 n`. -/
private lemma wpa_psiResidueClass_natCast_eq {q : ℕ} (b : ZMod q) (n : ℕ) :
    psiResidueClass b (n : ℝ)
      = ∑ k ∈ Finset.Icc 1 n,
        ArithmeticFunction.vonMangoldt.residueClass b k := by
  simp only [psiResidueClass, Nat.floor_natCast,
    ← Finset.Icc_add_one_left_eq_Ioc]
  rfl

/-- The `Finset.range` sum in the Wanted statement equals `psiResidueClass`. -/
private lemma wpa_sum_range_ite_mod_eq {q a : ℕ} (ha_lt : a < q) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1),
      if n % q = a then ArithmeticFunction.vonMangoldt n else 0)
      = psiResidueClass (a : ZMod q) (M : ℝ) := by
  have key : ∀ n : ℕ, (if n % q = a then ArithmeticFunction.vonMangoldt n else 0)
      = ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n := by
    intro n
    have hiff : ((n : ZMod q) = (a : ZMod q)) ↔ (n % q = a) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha_lt]
    by_cases h : n % q = a
    · have hmem : n ∈ {n : ℕ | ((n : ZMod q) = (a : ZMod q))} := hiff.mpr h
      rw [ite_eq_left h]
      exact (Set.indicator_of_mem hmem _).symm
    · have hmem : n ∉ {n : ℕ | ((n : ZMod q) = (a : ZMod q))} :=
        fun hm => h (hiff.mp hm)
      rw [ite_eq_right h]
      exact (Set.indicator_of_notMem hmem _).symm
  have h0 : (if 0 % q = a then ArithmeticFunction.vonMangoldt 0 else 0) = 0 := by
    split_ifs with h
    · exact ArithmeticFunction.map_zero
    · rfl
  calc (∑ n ∈ Finset.range (M + 1),
          if n % q = a then ArithmeticFunction.vonMangoldt n else 0)
      = ∑ n ∈ Finset.Icc 0 M,
          (if n % q = a then ArithmeticFunction.vonMangoldt n else 0) := by
        rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
    _ = (if 0 % q = a then ArithmeticFunction.vonMangoldt 0 else 0)
          + ∑ n ∈ Finset.Ioc 0 M,
            (if n % q = a then ArithmeticFunction.vonMangoldt n else 0) := by
        rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le M), Finset.sum_cons]
    _ = ∑ n ∈ Finset.Ioc 0 M,
          ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n := by
        rw [h0, zero_add]
        exact Finset.sum_congr rfl (fun n _ => key n)
    _ = psiResidueClass (a : ZMod q) (M : ℝ) := by
        rw [psiResidueClass, Nat.floor_natCast]

/-- `LFunctionTrivChar₁` does not vanish on `re s ≥ 1`. -/
private lemma wpa_LFunctionTrivChar₁_ne_zero {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  · unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero_of_ne hs1)
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inr hs1) hs)

/-- Laplace transform of a partial-sum function in exponential time. -/
private lemma wpa_hasLaplace_partialSum_exp (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, f k ≤ C * (n : ℝ))
    (s : ℂ) (hs : 1 < s.re) :
    HasLaplace (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ))
      s (LSeries (fun n => (f n : ℂ)) s / s) := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    norm_num at hs
  have hmono : Monotone (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k) := by
    intro t₁ t₂ h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc le_rfl
        (Nat.floor_mono (Real.exp_le_exp.mpr h))
    · intro k _ _
      exact hf k
  have hb : ∀ t : ℝ, 0 ≤ t →
      ‖(((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ)) : ℂ)‖
        ≤ C * Real.exp (1 * t) := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => hf k)]
    calc (∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k)
        ≤ C * (⌊Real.exp t⌋₊ : ℝ) := hbound _
      _ ≤ C * Real.exp t := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact Nat.floor_le (le_of_lt (Real.exp_pos t))
      _ = C * Real.exp (1 * t) := by rw [one_mul]
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      hmono.measurable).aestronglyMeasurable
  have hconv : LaplaceConvergent
      (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ)) s :=
    laplaceConvergent_of_norm_le_exp _ 1 C hmeas hC hb hs
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards with n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => hf k),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
      Real.rpow_one]
    exact hbound n
  have hL := LSeries_eq_mul_integral_of_nonneg f zero_le_one hs hO hf
  have hchange := MeasureTheory.integral_comp_exp_Ioi
    (fun y : ℝ => (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (f k : ℂ)) *
      ((y : ℝ) : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at hchange
  have hpt : ∀ u : ℝ, Complex.exp (-s * (u : ℂ))
        • ((((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, f k : ℝ))) : ℂ)
      = Real.exp u •
        ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (f k : ℂ)) *
          (((Real.exp u : ℝ)) : ℂ) ^ (-(s + 1))) := by
    intro u
    have he : ((((Real.exp u : ℝ))) : ℂ) ≠ 0 := by
      exact_mod_cast Real.exp_ne_zero u
    have hlog : Complex.log ((((Real.exp u : ℝ))) : ℂ) = (u : ℂ) := by
      rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos u)), Real.log_exp]
    have hcpow : ((((Real.exp u : ℝ))) : ℂ) ^ (-(s + 1))
        = Complex.exp (-(s + 1) * (u : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero he, hlog]
      congr 1
      ring
    have hexp : ((((Real.exp u : ℝ))) : ℂ) = Complex.exp (u : ℂ) :=
      Complex.ofReal_exp u
    have e : Complex.exp (u : ℂ) * Complex.exp (-(s + 1) * (u : ℂ))
        = Complex.exp (-s * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [Complex.ofReal_sum, RCLike.real_smul_eq_coe_mul, smul_eq_mul, hcpow,
      RCLike.ofReal_eq_complex_ofReal, hexp]
    linear_combination
      -(∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (f k : ℂ)) * e
  have hval : laplace
      (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ)) s
      = LSeries (fun n => (f n : ℂ)) s / s := by
    have hlap : laplace
          (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ)) s
        = ∫ u : ℝ in Set.Ioi 0, Real.exp u •
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (f k : ℂ)) *
            (((Real.exp u : ℝ)) : ℂ) ^ (-(s + 1))) := by
      unfold laplace
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => hpt u)
    rw [hlap, hchange, hL, mul_div_cancel_left₀ _ hs0]
  exact ⟨hconv, hval⟩

/-- The residue-class auxiliary function is analytic on `re s ≥ 1`. -/
private lemma wpa_analyticOnNhd_LFunctionResidueClassAux {q : ℕ} [NeZero q]
    (b : ZMod q) :
    AnalyticOnNhd ℂ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b)
      {s | 1 ≤ s.re} := by
  classical
  have hT : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ q)
      Set.univ :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn.analyticOnNhd
      isOpen_univ
  have hT' : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ q)
      {s | 1 ≤ s.re} := hT.mono (Set.subset_univ _)
  have hTd : AnalyticOnNhd ℂ
      (deriv (DirichletCharacter.LFunctionTrivChar₁ q)) {s | 1 ≤ s.re} :=
    hT.deriv.mono (Set.subset_univ _)
  have hdivT : AnalyticOnNhd ℂ
      (fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
        DirichletCharacter.LFunctionTrivChar₁ q s) {s | 1 ≤ s.re} :=
    hTd.div hT' (fun x hx => wpa_LFunctionTrivChar₁_ne_zero hx)
  have hnegT : AnalyticOnNhd ℂ
      (fun s => -(deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
        DirichletCharacter.LFunctionTrivChar₁ q s)) {s | 1 ≤ s.re} :=
    hdivT.neg
  have hsum : AnalyticOnNhd ℂ
      (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
        fun s => ((χ b⁻¹ : ℂ) *
          deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s))
      {s | 1 ≤ s.re} := by
    apply Finset.analyticOnNhd_sum _ _
    intro χ hχ
    have hne : χ ≠ 1 := by
      simpa only [Finset.mem_compl, Finset.mem_singleton] using hχ
    have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
      (DirichletCharacter.differentiable_LFunction hne).differentiableOn.analyticOnNhd
        isOpen_univ
    have hL' : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
        {s | 1 ≤ s.re} := hL.mono (Set.subset_univ _)
    have hLd : AnalyticOnNhd ℂ
        (deriv (DirichletCharacter.LFunction χ)) {s | 1 ≤ s.re} :=
      hL.deriv.mono (Set.subset_univ _)
    have hdiv : AnalyticOnNhd ℂ
        (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s) {s | 1 ≤ s.re} :=
      hLd.div hL'
        (fun x hx =>
          DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hne) hx)
    have hmul : AnalyticOnNhd ℂ
        (fun s => (χ b⁻¹ : ℂ) *
          (deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)) {s | 1 ≤ s.re} :=
      analyticOnNhd_const.mul hdiv
    simpa only [mul_div_assoc] using hmul
  have hcomb : AnalyticOnNhd ℂ
      ((fun _ => (q.totient : ℂ)⁻¹) *
        ((-(fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
          DirichletCharacter.LFunctionTrivChar₁ q s)) -
        ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
          fun s => ((χ b⁻¹ : ℂ) *
            deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)))
      {s | 1 ≤ s.re} :=
    analyticOnNhd_const.mul (hnegT.sub hsum)
  have hEq : ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b =
      ((fun _ => (q.totient : ℂ)⁻¹) *
        ((-(fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
          DirichletCharacter.LFunctionTrivChar₁ q s)) -
        ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
          fun s => ((χ b⁻¹ : ℂ) *
            deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s))) := by
    unfold ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux
    funext s
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply,
      neg_div, mul_div_assoc]
  rw [hEq]
  exact hcomb

/-- The continuation of the Laplace transform of the error function. -/
private noncomputable def wpaPsiErrorCont {q : ℕ} [NeZero q] (b : ZMod q)
    (s : ℂ) : ℂ :=
  ((q.totient : ℂ) *
      ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b (s + 1) - 1) /
    (s + 1)

/-- Analyticity of the error continuation on `re s ≥ 0`. -/
private lemma wpa_analyticOnNhd_psiErrorCont {q : ℕ} [NeZero q] (b : ZMod q) :
    AnalyticOnNhd ℂ (wpaPsiErrorCont b) {s | 0 ≤ s.re} := by
  have hbase := wpa_analyticOnNhd_LFunctionResidueClassAux (q := q) b
  have hAnalytic : AnalyticOnNhd ℂ (fun s : ℂ => s + 1) {s | 0 ≤ s.re} :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hMaps : Set.MapsTo (fun s : ℂ => s + 1) {s | 0 ≤ s.re}
      {s | 1 ≤ s.re} := by
    intro x hx
    change (1 : ℝ) ≤ ((fun s : ℂ => s + 1) x).re
    have hx' : (0 : ℝ) ≤ x.re := hx
    have hAdd : ((fun s : ℂ => s + 1) x).re = x.re + 1 := by simp
    linarith
  have hComp : AnalyticOnNhd ℂ
      (fun s : ℂ => (q.totient : ℂ) *
        ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b (s + 1))
      {s | 0 ≤ s.re} :=
    analyticOnNhd_const.mul (hbase.comp hAnalytic hMaps)
  have hSub : AnalyticOnNhd ℂ
      (fun s : ℂ => (q.totient : ℂ) *
        ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b (s + 1) - 1)
      {s | 0 ≤ s.re} :=
    hComp.sub analyticOnNhd_const
  have hNe : ∀ s ∈ {s : ℂ | 0 ≤ s.re}, (s + 1 : ℂ) ≠ 0 := by
    intro s hs h0
    simp only [Set.mem_ofPred_eq] at hs
    have hZero : (s + 1).re = 0 := by simp [h0]
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hDiv := hSub.div hAnalytic hNe
  exact hDiv

/-- The normalized residue-class psi error function. -/
private noncomputable def wpaPsiError {q : ℕ} (b : ZMod q) (t : ℝ) : ℝ :=
  (q.totient : ℝ) * psiResidueClass b (Real.exp t) * Real.exp (-t) - 1

/-- Measurability of the normalized error function. -/
private lemma wpa_measurable_psiError {q : ℕ} (b : ZMod q) :
    Measurable (wpaPsiError b) := by
  unfold wpaPsiError
  exact ((measurable_const.mul ((wpa_psiResidueClass_mono b).measurable.comp
    Real.measurable_exp)).mul
    (Real.measurable_exp.comp measurable_neg)).sub_const 1

/-- Uniform bound for the normalized error function. -/
private lemma wpa_abs_psiError_le {q : ℕ} (b : ZMod q) (t : ℝ) :
    |wpaPsiError b t| ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
  have hnn : (0 : ℝ) ≤ psiResidueClass b (Real.exp t) :=
    wpa_psiResidueClass_nonneg b _
  have hle : psiResidueClass b (Real.exp t)
      ≤ (Real.log 4 + 4) * Real.exp t :=
    wpa_psiResidueClass_le_mul_self b (le_of_lt (Real.exp_pos t))
  have hphi_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hexp_pos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hprod_nn : (0 : ℝ) ≤ (q.totient : ℝ) *
      psiResidueClass b (Real.exp t) * Real.exp (-t) :=
    mul_nonneg (mul_nonneg hphi_nn hnn) (le_of_lt hexp_pos)
  have hprod_le : (q.totient : ℝ) * psiResidueClass b (Real.exp t) *
      Real.exp (-t) ≤ (q.totient : ℝ) * (Real.log 4 + 4) := by
    calc (q.totient : ℝ) * psiResidueClass b (Real.exp t) * Real.exp (-t)
        ≤ ((q.totient : ℝ) * ((Real.log 4 + 4) * Real.exp t)) *
          Real.exp (-t) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hexp_pos)
          exact mul_le_mul_of_nonneg_left hle hphi_nn
      _ = (q.totient : ℝ) * (Real.log 4 + 4) *
          (Real.exp t * Real.exp (-t)) := by ring
      _ = (q.totient : ℝ) * (Real.log 4 + 4) := by rw [hexp, mul_one]
  have hB_nn : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) :=
    mul_nonneg hphi_nn (by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith)
  rw [abs_le]
  unfold wpaPsiError
  constructor <;> linarith

/-- Laplace transform of the normalized error function. -/
private lemma wpa_hasLaplace_psiError {q : ℕ} [NeZero q] (b : ZMod q)
    (hb : IsUnit b) (s : ℂ) (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      (wpaPsiErrorCont b s) := by
  have hs1 : (1 : ℝ) < (s + 1).re := by
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log 4 :=
    Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hS := wpa_hasLaplace_partialSum_exp
    (ArithmeticFunction.vonMangoldt.residueClass b)
    (fun n => ArithmeticFunction.vonMangoldt.residueClass_nonneg b n)
    (Real.log 4 + 4) (by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith)
    (fun n => by
      rw [← wpa_psiResidueClass_natCast_eq b n]
      exact wpa_psiResidueClass_le_mul_self b (Nat.cast_nonneg n))
    (s + 1) hs1
  obtain ⟨hSconv, hSval⟩ := hS
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    norm_num at hs
  have hs1ne : s + 1 ≠ 0 := by
    intro h0
    have hZero : (s + 1).re = 0 := by simp [h0]
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hphi : (q.totient : ℂ) ≠ 0 := by
    have hpos : 0 < q.totient :=
      Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast hpos.ne'
  have hNeg : (-s).re < 0 := by
    have hEq : (-s).re = -s.re := by simp
    linarith
  have hBaseInt := integrableOn_exp_mul_complex_Ioi hNeg 0
  have hEqFun2 : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      = (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) := by
    funext t
    simp only [smul_eq_mul, mul_one, neg_mul]
  have h2 : IntegrableOn
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      (Set.Ioi 0) := by
    rw [hEqFun2]
    exact hBaseInt
  have hExpEq : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) *
      ((Real.exp (-t) : ℝ) : ℂ)
      = Complex.exp (-(s + 1) * (t : ℂ)) := by
    intro t
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpsi : ∀ t : ℝ, psiResidueClass b (Real.exp t)
      = ∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b k := by
    intro t
    have e : Finset.Icc 1 ⌊Real.exp t⌋₊
        = Finset.Ioc 0 ⌊Real.exp t⌋₊ := by
      rw [← Finset.Icc_add_one_left_eq_Ioc]
      rfl
    rw [e, psiResidueClass]
  have hpsiC : ∀ t : ℝ, ((psiResidueClass b (Real.exp t) : ℝ) : ℂ)
      = ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ) :=
    fun t => congrArg _ (hpsi t)
  have hPoint : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) •
        ((wpaPsiError b t : ℝ) : ℂ)
      = (Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
        - (Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) := by
    intro t
    have hE := hExpEq t
    simp only [wpaPsiError, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_natCast, hpsiC]
    linear_combination
      ((q.totient : ℂ) *
        ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)) * hE
  have hEqFun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) •
        ((wpaPsiError b t : ℝ) : ℂ))
      = (fun t : ℝ => (Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
        - (Complex.exp (-s * (t : ℂ)) • (1 : ℂ))) := by
    funext t
    exact hPoint t
  have h1e : (fun t : ℝ => Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
      = (fun t : ℝ => (q.totient : ℂ) *
        (Complex.exp (-(s + 1) * (t : ℂ)) •
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ))) := by
    funext t
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have h1 : IntegrableOn (fun t : ℝ =>
      Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
      (Set.Ioi 0) := by
    rw [h1e]
    exact hSconv.const_mul _
  have hB : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
    have hphi_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    have hle : (0 : ℝ) ≤ Real.log 4 + 4 := by linarith
    have := mul_nonneg hphi_nn hle
    linarith
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(((wpaPsiError b t : ℝ)) : ℂ)‖
        ≤ ((q.totient : ℝ) * (Real.log 4 + 4) + 1) * Real.exp (0 * t) := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs, zero_mul, Real.exp_zero, mul_one]
    exact wpa_abs_psiError_le b t
  have hmeasC : AEStronglyMeasurable
      (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Complex.measurable_ofReal.comp
      (wpa_measurable_psiError b)).aestronglyMeasurable
  have hconv0 : LaplaceConvergent
      (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s :=
    laplaceConvergent_of_norm_le_exp _ 0 _ hmeasC hB hbound hs
  have hIntEq : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • ((wpaPsiError b t : ℝ) : ℂ))
      = (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-(s + 1) * (t : ℂ)) •
            ((q.totient : ℂ) *
              ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
                ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
        - (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) := by
    rw [hEqFun]
    exact MeasureTheory.integral_sub h1 h2
  have hLap : laplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      = (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • ((wpaPsiError b t : ℝ) : ℂ)) := rfl
  have hThetaInt : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-(s + 1) * (t : ℂ)) •
          ((q.totient : ℂ) *
            ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
              ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
      = (q.totient : ℂ) *
        (LSeries (fun n =>
          (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ))
          (s + 1) / (s + 1)) := by
    have hSint : (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-(s + 1) * (t : ℂ)) •
            ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
              ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ))
        = LSeries (fun n =>
          (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ)) (s + 1) /
          (s + 1) := hSval
    rw [h1e, MeasureTheory.integral_const_mul, hSint]
  have hRw : (∫ t : ℝ in Set.Ioi 0,
      Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) = 1 / s := by
    have hEqInt : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
        = (∫ t : ℝ in Set.Ioi 0, Complex.exp ((-s) * (t : ℂ))) := by
      congr 1
    have hConstBase := integral_exp_mul_complex_Ioi hNeg 0
    have hField : (-1 : ℂ) / (-s) = 1 / s := by field_simp
    have hRw0 : (∫ t : ℝ in Set.Ioi 0, Complex.exp ((-s) * (t : ℂ)))
        = (-1 : ℂ) / (-s) := by
      simpa using hConstBase
    rw [hEqInt, hRw0, hField]
  have hVal : laplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      = (q.totient : ℂ) *
        (LSeries (fun n =>
          (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ))
          (s + 1) / (s + 1)) - 1 / s := by
    rw [hLap, hIntEq, hThetaInt, hRw]
  have hmem : s + 1 ∈ {s : ℂ | 1 < s.re} := hs1
  have hAuxEq := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
    (a := b) hb hmem
  have hAuxEq' : ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b
        (s + 1)
      = LSeries (fun n =>
        (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ)) (s + 1)
        - (q.totient : ℂ)⁻¹ / ((s + 1) - 1) := hAuxEq
  have hFinal : laplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      = wpaPsiErrorCont b s := by
    rw [hVal]
    unfold wpaPsiErrorCont
    rw [hAuxEq']
    have hsub : s + 1 - 1 = s := by ring
    rw [hsub]
    field_simp
    ring
  exact ⟨hconv0, hFinal⟩

/-- Convergence of the integral of the error function. -/
private lemma wpa_tendsto_integral_psiError {q : ℕ} [NeZero q] (b : ZMod q)
    (hb : IsUnit b) :
    ∃ L : ℝ, Filter.Tendsto
      (fun U : ℝ => ∫ u : ℝ in (0 : ℝ)..U, wpaPsiError b u)
      Filter.atTop (nhds L) := by
  have hmeas : Measurable (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (wpa_measurable_psiError b)
  have hfmeas : AEStronglyMeasurable
      (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hmeas.aestronglyMeasurable
  have hB : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
    have hphi_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    have hle : (0 : ℝ) ≤ Real.log 4 + 4 := by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith
    have := mul_nonneg hphi_nn hle
    linarith
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(((wpaPsiError b t : ℝ)) : ℂ)‖
        ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact wpa_abs_psiError_le b t
  have hmain := newman_tauberian (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ))
    ((q.totient : ℝ) * (Real.log 4 + 4) + 1) hfmeas hB hbound
    (wpaPsiErrorCont b)
    (wpa_analyticOnNhd_psiErrorCont b)
    (fun s hs => wpa_hasLaplace_psiError b hb s hs)
  refine ⟨(wpaPsiErrorCont b 0).re, ?_⟩
  have hcast : ∀ U : ℝ,
      ((∫ u : ℝ in (0 : ℝ)..U, ((wpaPsiError b u : ℝ) : ℂ)).re)
        = ∫ u : ℝ in (0 : ℝ)..U, wpaPsiError b u := by
    intro U
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have h2 := (Complex.continuous_re.tendsto
    (wpaPsiErrorCont b 0)).comp hmain
  have e : (fun U : ℝ => ∫ u : ℝ in (0 : ℝ)..U, wpaPsiError b u)
      = Complex.re ∘ (fun T : ℝ => ∫ u : ℝ in (0 : ℝ)..T,
        ((wpaPsiError b u : ℝ) : ℂ)) :=
    funext fun U => (hcast U).symm
  rw [e]
  exact h2

/-- Substitution `t = e^u` turns the Chebyshev-style integral into `∫ H`. -/
private lemma wpa_integral_psi_sub_div_sq_eq {q : ℕ} (b : ZMod q) (x : ℝ)
    (hx : 1 ≤ x) :
    ∫ t : ℝ in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2
      = ∫ u : ℝ in (0 : ℝ)..Real.log x, wpaPsiError b u := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have himg : Set.Ioc 1 x = Real.exp '' Set.Ioc 0 (Real.log x) := by
    rw [Real.image_exp_Ioc, Real.exp_zero, Real.exp_log hx0]
  have hpt : ∀ u : ℝ, |Real.exp u| • (((q.totient : ℝ) *
      psiResidueClass b (Real.exp u) - Real.exp u) / (Real.exp u) ^ 2)
      = wpaPsiError b u := by
    intro u
    have hne : Real.exp u ≠ 0 := Real.exp_ne_zero u
    have hexp : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [abs_of_pos (Real.exp_pos u), smul_eq_mul]
    unfold wpaPsiError
    field_simp
    linear_combination
      (-((q.totient : ℝ) * psiResidueClass b (Real.exp u))) * hexp
  have hchange : (∫ t : ℝ in Real.exp '' Set.Ioc 0 (Real.log x),
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • (((q.totient : ℝ) * psiResidueClass b (Real.exp u) -
          Real.exp u) / (Real.exp u) ^ 2) :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioc
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      (Real.exp_injective.injOn) _
  have step1 : (∫ t : ℝ in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • (((q.totient : ℝ) * psiResidueClass b (Real.exp u) -
          Real.exp u) / (Real.exp u) ^ 2) := by
    rw [himg]
    exact hchange
  have step2 : (∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • (((q.totient : ℝ) * psiResidueClass b (Real.exp u) -
          Real.exp u) / (Real.exp u) ^ 2))
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x), wpaPsiError b u :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => hpt u)
  have step3 : (∫ u : ℝ in Set.Ioc 0 (Real.log x), wpaPsiError b u)
      = ∫ u : ℝ in (0 : ℝ)..Real.log x, wpaPsiError b u :=
    (intervalIntegral.integral_of_le hlog).symm
  exact step1.trans (step2.trans step3)

/-- Convergence of the Chebyshev-style integral. -/
private lemma wpa_tendsto_integral_psi_sub_div_sq {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    ∃ L : ℝ, Filter.Tendsto
      (fun x => ∫ t : ℝ in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      Filter.atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := wpa_tendsto_integral_psiError b hb
  refine ⟨L, ?_⟩
  have hcomp : Filter.Tendsto
      (fun x : ℝ => ∫ u : ℝ in (0 : ℝ)..Real.log x, wpaPsiError b u)
      Filter.atTop (𝓝 L) :=
    hL.comp Real.tendsto_log_atTop
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have hev := h1.mono
    (fun x hx => (wpa_integral_psi_sub_div_sq_eq b x hx).symm)
  exact Filter.Tendsto.congr' hev hcomp

/-- **Prime number theorem for Chebyshev's function in a reduced residue class.** Let $q \ge 1$
be an integer, let $b$ be a unit of $\mathbb{Z}/q\mathbb{Z}$, let $\Lambda$ be the von Mangoldt
function and let $\varphi$ be Euler's totient function. For real $x$ let $\psi(x; q, b)$ be the
sum of $\Lambda(n)$ over the integers $1 \le n \le x$ with $n \equiv b \pmod{q}$. Then
$\psi(x; q, b)/x \to 1/\varphi(q)$ as the real number $x$ tends to infinity. -/
public lemma tendsto_psiResidueClass_div_self {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    Filter.Tendsto (fun x : ℝ => psiResidueClass b x / x) Filter.atTop
      (nhds ((q.totient : ℝ)⁻¹)) := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) :=
    Nat.cast_pos.mpr
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hphi_ne : (q.totient : ℝ) ≠ 0 := ne_of_gt hphi_pos
  obtain ⟨L, hL⟩ := wpa_tendsto_integral_psi_sub_div_sq b hb
  have hmono : MonotoneOn (fun x : ℝ => (q.totient : ℝ) * psiResidueClass b x)
      (Set.Ici 1) := by
    intro x _ y _ hxy
    exact mul_le_mul_of_nonneg_left
      (wpa_psiResidueClass_mono b hxy) (le_of_lt hphi_pos)
  have hisEq : (fun x : ℝ => (q.totient : ℝ) * psiResidueClass b x)
      ~[Filter.atTop] (fun x : ℝ => x) :=
    Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq _
      hmono ⟨L, hL⟩
  have hlim1 : Filter.Tendsto
      (fun x : ℝ => ((q.totient : ℝ) * psiResidueClass b x) / x)
      Filter.atTop (nhds 1) := by
    have hz : ∀ᶠ x : ℝ in Filter.atTop, (fun x : ℝ => x) x ≠ 0 := by
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      exact ne_of_gt hx
    exact (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hisEq
  have e : (fun x : ℝ => psiResidueClass b x / x)
      = (fun x : ℝ => (q.totient : ℝ)⁻¹ *
        (((q.totient : ℝ) * psiResidueClass b x) / x)) := by
    funext x
    field_simp
  rw [e]
  have hmul := hlim1.const_mul ((q.totient : ℝ)⁻¹)
  simpa using hmul

/-- **Mertens' theorem in arithmetic progressions.** Let $q \ge 1$ be an integer, let $b$ be a
unit of $\mathbb{Z}/q\mathbb{Z}$, let $\Lambda$ be the von Mangoldt function and let $\varphi$ be
Euler's totient function. There is a real constant $C$ such that for every real $x \ge 1$,
$$
\left| \sum_{\substack{1 \le n \le x \\ n \equiv b \pmod{q}}} \frac{\Lambda(n)}{n} -
\frac{\log x}{\varphi(q)} \right| \le C.
$$
-/
public lemma exists_abs_sum_residueClass_div_sub_log_le {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
        Real.log x / (q.totient : ℝ)| ≤ C := by
  have hc0 : ArithmeticFunction.vonMangoldt.residueClass b 0 = 0 :=
    ArithmeticFunction.vonMangoldt.residueClass_apply_zero b
  have hφ : (0 : ℝ) < (q.totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hS : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass b k = psiResidueClass b t := by
    intro t
    rw [psiResidueClass, Finset.Icc_eq_cons_Ioc (Nat.zero_le _),
      Finset.sum_cons, hc0, zero_add]
  have hdiff : ∀ x : ℝ, ∀ t ∈ Set.Icc 1 x,
      DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro x t ht
    rw [Set.mem_Icc] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact (hasDerivAt_inv ht0).differentiableAt
  have hint : ∀ x : ℝ,
      IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc 1 x) := by
    intro x
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuous_pow 2).continuousOn
    intro t ht
    rw [Set.mem_Icc] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hLHS : ∀ N : ℕ, ∑ k ∈ Finset.Icc 0 N, ((k : ℝ))⁻¹ *
      ArithmeticFunction.vonMangoldt.residueClass b k
      = ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) := by
    intro N
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hc0]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro k _
    exact inv_mul_eq_div _ _
  have hmain : ∀ x : ℝ, x⁻¹ * psiResidueClass b x = psiResidueClass b x / x := by
    intro x
    exact inv_mul_eq_div _ _
  have hint2 : ∀ x : ℝ, (∫ t in Set.Ioc 1 x,
      deriv (fun t : ℝ => t⁻¹) t * psiResidueClass b t)
      = - ∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2 := by
    intro x
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t _
    change deriv (fun t : ℝ => t⁻¹) t * psiResidueClass b t =
      -(psiResidueClass b t / t ^ 2)
    rw [deriv_inv, neg_mul, inv_mul_eq_div]
  have habel : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))
      = psiResidueClass b x / x
        + ∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2 := by
    intro x hx
    have hA := sum_mul_eq_sub_integral_mul₀ (f := fun t : ℝ => t⁻¹)
      (ArithmeticFunction.vonMangoldt.residueClass b) hc0 x (hdiff x) (hint x)
    simp only [hS] at hA
    rw [hLHS, hmain, hint2, sub_neg_eq_add] at hA
    exact hA
  have he_int : ∀ x : ℝ, IntegrableOn
      (fun t => ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      (Set.Ioc 1 x) volume := by
    intro x
    have hfin : volume (Set.Ioc (1 : ℝ) x) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_
      ((q.totient : ℝ) * (Real.log 4 + 4) + 1) ?_
    · have hψ : Measurable (fun t : ℝ => psiResidueClass b t) :=
        (wpa_psiResidueClass_mono b).measurable
      exact (((measurable_const.mul hψ).sub measurable_id).div
        (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.mem_Ioc] at ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht1)
      have htnn : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
      have hψnn : 0 ≤ psiResidueClass b t := wpa_psiResidueClass_nonneg b t
      have hψle : psiResidueClass b t ≤ (Real.log 4 + 4) * t :=
        wpa_psiResidueClass_le_mul_self b htnn
      have hKnn : (0 : ℝ) ≤ Real.log 4 + 4 := by
        have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := le_of_lt hφ
      have hCnn : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 :=
        add_nonneg (mul_nonneg hφnn hKnn) zero_le_one
      have h2 : ((q.totient : ℝ) * (Real.log 4 + 4)) * t
          ≥ (q.totient : ℝ) * psiResidueClass b t := by
        have h := mul_le_mul_of_nonneg_left hψle hφnn
        rwa [mul_assoc]
      have h3 : (0 : ℝ) ≤ ((q.totient : ℝ) * (Real.log 4 + 4)) * t :=
        mul_nonneg (mul_nonneg hφnn hKnn) htnn
      have hnum : ‖(q.totient : ℝ) * psiResidueClass b t - t‖
          ≤ ((q.totient : ℝ) * (Real.log 4 + 4) + 1) * t := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [h2, h3, mul_nonneg hφnn hψnn, htnn]
      have ht2nn : (0 : ℝ) ≤ t ^ 2 := pow_nonneg htnn 2
      have ht2pos : (0 : ℝ) < t ^ 2 := pow_pos (lt_of_lt_of_le zero_lt_one ht1) 2
      have ht2le : t ≤ t ^ 2 := by
        calc t = t * 1 := (mul_one t).symm
          _ ≤ t * t := mul_le_mul_of_nonneg_left ht1 htnn
          _ = t ^ 2 := (sq t).symm
      calc ‖((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2‖
          = ‖(q.totient : ℝ) * psiResidueClass b t - t‖ / t ^ 2 := by
            simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg ht2nn]
        _ ≤ (((q.totient : ℝ) * (Real.log 4 + 4) + 1) * t) / t ^ 2 :=
            div_le_div_of_nonneg_right hnum ht2nn
        _ ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
            rw [div_le_iff₀ ht2pos]
            exact mul_le_mul_of_nonneg_left ht2le hCnn
  have hg_int : ∀ x : ℝ, IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) volume := by
    intro x
    have hIcc : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) volume := by
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.inv₀ continuous_id.continuousOn
      intro t ht
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hlog : ∀ x : ℝ, 1 ≤ x →
      (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ * t⁻¹)
        = ((q.totient : ℝ))⁻¹ * Real.log x := by
    intro x hx
    have hbase : (∫ t in Set.Ioc 1 x, t⁻¹) = Real.log x := by
      rw [(intervalIntegral.integral_of_le hx).symm,
        integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hx), div_one]
    calc (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ * t⁻¹)
        = ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x, t⁻¹ := by
          simp only [← smul_eq_mul]
          exact MeasureTheory.integral_const_mul _ _
      _ = ((q.totient : ℝ))⁻¹ * Real.log x := by rw [hbase]
  have hsplit : ∀ x : ℝ, 1 ≤ x →
      (∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2)
      = ((q.totient : ℝ))⁻¹ *
          (∫ t in Set.Ioc 1 x,
            ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
        + ((q.totient : ℝ))⁻¹ * Real.log x := by
    intro x hx
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    have hpt : ∀ t : ℝ, psiResidueClass b t / t ^ 2
        = ((q.totient : ℝ))⁻¹ *
            (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
          + ((q.totient : ℝ))⁻¹ * t⁻¹ := by
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp
        ring
    have h1 : IntegrableOn
        (fun t => ((q.totient : ℝ))⁻¹ *
          (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2))
        (Set.Ioc 1 x) volume := (he_int x).const_mul _
    have h2 : IntegrableOn (fun t : ℝ => ((q.totient : ℝ))⁻¹ * t⁻¹)
        (Set.Ioc 1 x) volume := (hg_int x).const_mul _
    have hval : (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ *
          (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2))
        = ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x,
          (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2) := by
      simp only [← smul_eq_mul]
      exact MeasureTheory.integral_const_mul _ _
    calc (∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2)
        = ∫ t in Set.Ioc 1 x, (((q.totient : ℝ))⁻¹ *
            (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
            + ((q.totient : ℝ))⁻¹ * t⁻¹) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpt t)
      _ = (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ *
            (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2))
          + ∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ * t⁻¹ :=
          MeasureTheory.integral_add h1 h2
      _ = ((q.totient : ℝ))⁻¹ *
            (∫ t in Set.Ioc 1 x,
              ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
          + ((q.totient : ℝ))⁻¹ * Real.log x := by
          rw [hval, hlog x hx]
  obtain ⟨L, hL⟩ := wpa_tendsto_integral_psi_sub_div_sq b hb
  have hPNT := tendsto_psiResidueClass_div_self b hb
  have hI : Filter.Tendsto
      (fun x => ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      Filter.atTop (nhds (((q.totient : ℝ))⁻¹ * L)) :=
    hL.const_mul _
  have hE : Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))
        - Real.log x / (q.totient : ℝ))
      Filter.atTop
      (nhds (((q.totient : ℝ))⁻¹ + ((q.totient : ℝ))⁻¹ * L)) := by
    have hev : (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))
        - Real.log x / (q.totient : ℝ))
        =ᶠ[Filter.atTop] (fun x => psiResidueClass b x / x
          + ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x,
            ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      rw [habel x hx, hsplit x hx]
      ring
    exact Filter.Tendsto.congr' hev.symm (hPNT.add hI)
  -- Uniform bound extraction: the error is convergent, hence bounded at infinity;
  -- on the compact head it is a finite sum plus a bounded log term.
  set M : ℝ := ((q.totient : ℝ))⁻¹ + ((q.totient : ℝ))⁻¹ * L with hM
  obtain ⟨X₀, hX₀⟩ := (Metric.tendsto_atTop.mp hE) 1 one_pos
  set X₁ : ℝ := max X₀ 1 with hX₁
  have hX₁ge : 1 ≤ X₁ := le_max_right _ _
  set S : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊X₁⌋₊,
    |ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)| with hS
  have hlogX₁ : 0 ≤ Real.log X₁ := Real.log_nonneg hX₁ge
  refine ⟨max (|M| + 1) (S + Real.log X₁ / (q.totient : ℝ)), fun x hx => ?_⟩
  have hφnn : 0 ≤ (q.totient : ℝ) := le_of_lt hφ
  by_cases hle : x ≤ X₁
  · -- Compact head: the finite sum grows monotonically and log is monotone.
    have hsub : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 ⌊X₁⌋₊ :=
      Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hle)
    have hsum : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))| ≤ S :=
      calc |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))|
          ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            |ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => abs_nonneg _)
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hlog : |Real.log x| ≤ Real.log X₁ := by
      rw [abs_of_nonneg (Real.log_nonneg hx)]
      exact Real.log_le_log hxpos hle
    have hdiv : |Real.log x / (q.totient : ℝ)| ≤ Real.log X₁ / (q.totient : ℝ) := by
      rw [abs_div, abs_of_nonneg hφnn]
      exact div_le_div_of_nonneg_right hlog hφnn
    calc |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
            Real.log x / (q.totient : ℝ)|
        ≤ |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))| +
          |Real.log x / (q.totient : ℝ)| := abs_sub _ _
      _ ≤ S + Real.log X₁ / (q.totient : ℝ) := add_le_add hsum hdiv
      _ ≤ max (|M| + 1) (S + Real.log X₁ / (q.totient : ℝ)) := le_max_right _ _
  · -- Tail: within distance 1 of the limit.
    have hlt : X₁ < x := lt_of_not_ge hle
    have hx₀ : x ≥ X₀ := le_trans (le_max_left _ _) (le_of_lt hlt)
    have h := hX₀ x hx₀
    rw [Real.dist_eq] at h
    calc |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
            Real.log x / (q.totient : ℝ)|
        ≤ |M| + 1 := by
          have htri : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
              ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
              Real.log x / (q.totient : ℝ)| - |M|
              ≤ |((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
                ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
                Real.log x / (q.totient : ℝ)) - M| :=
            abs_sub_abs_le_abs_sub _ _
          linarith [h]
      _ ≤ max (|M| + 1) (S + Real.log X₁ / (q.totient : ℝ)) := le_max_left _ _

end Chebyshev

@[expose] public section

namespace Chebyshev

/--
**Weak prime number theorem in arithmetic progressions.** Let $q$ and $a$ be natural numbers with
$a < q$ and $\gcd(a, q) = 1$, let $\Lambda$ be the von Mangoldt function and let $\varphi$ be
Euler's totient function. Then, as $N \to \infty$ through the natural numbers,
$$
\frac{1}{N} \sum_{\substack{0 \le n < N \\ n \equiv a \pmod{q}}} \Lambda(n) \to
\frac{1}{\varphi(q)}.
$$

Proves `Wanted` entry `weakPNT_arithmeticProgression`.

Source: the proved theorem
`PrimeNumberTheoremAnd.WeakPNT_AP` in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), revision
`be5e07e04cde20c5ceabf63759bd097a9c88173f`, and its use in
[arXiv:2608.24035](https://arxiv.org/abs/2608.24035). Lean preserves the source's natural
representative and half-open `Finset.range` normalization, while omitting the redundant assumption
`1 ≤ q`, which follows from `a < q`.
-/
public theorem weakPNT_arithmeticProgression {q a : ℕ}
    (ha : Nat.Coprime a q) (ha_lt : a < q) :
    Filter.Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
            if n % q = a then ArithmeticFunction.vonMangoldt n else 0) / (N : ℝ))
      Filter.atTop (nhds (1 / (Nat.totient q : ℝ))) := by
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le a) ha_lt
  have : NeZero q := ⟨by omega⟩
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hqpos)
  have hb : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hpsi_div := tendsto_psiResidueClass_div_self (q := q) (a : ZMod q) hb
  have hseq : Filter.Tendsto
      (fun M : ℕ => psiResidueClass (a : ZMod q) (M : ℝ) / (M : ℝ))
      Filter.atTop (nhds (((Nat.totient q : ℝ))⁻¹)) :=
    hpsi_div.comp tendsto_natCast_atTop_atTop
  have hfrac : Filter.Tendsto (fun M : ℕ => ((M : ℝ) / ((M : ℝ) + 1)))
      Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hmul := hseq.mul hfrac
  have hlim : Filter.Tendsto
      (fun M : ℕ => (psiResidueClass (a : ZMod q) (M : ℝ) / (M : ℝ)) *
        ((M : ℝ) / ((M : ℝ) + 1)))
      Filter.atTop (nhds (1 / (Nat.totient q : ℝ))) := by
    rw [one_div]
    simpa using hmul
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  show (psiResidueClass (a : ZMod q) ↑M / ↑M) * (↑M / (↑M + 1))
    = (∑ n ∈ Finset.range (M + 1),
      if n % q = a then ArithmeticFunction.vonMangoldt n else 0) / (↑(M + 1))
  rw [wpa_sum_range_ite_mod_eq ha_lt M]
  have hM0 : ((M : ℝ)) ≠ 0 := by
    exact_mod_cast (by omega : M ≠ 0)
  have hM1 : ((M : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    exact ne_of_gt this
  push_cast
  field_simp

end Chebyshev
