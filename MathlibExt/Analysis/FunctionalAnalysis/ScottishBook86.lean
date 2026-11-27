/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Banach’s Scottish Book Problem 86

A normalized real Fourier system on a proper subinterval of `[0, 1]` leaves too little
room for a new orthogonal unit function with the same pointwise bound.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted

open MeasureTheory

@[expose] public section

/-- **Lebesgue measure on the unit interval (Scottish Book Problem 86).** Lebesgue measure on
$\mathbb{R}$ restricted to the unit interval $[0, 1]$, the ambient measure for Problem 86. -/
noncomputable def scottishBook86Measure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/-- **Scottish Book Problem 86 (Banach).** The claim that for every real $M > 0$ and every
sequence $(\varphi_n)_{n \in \mathbb{N}}$ of functions $\mathbb{R} \to \mathbb{R}$ that are
almost everywhere measurable on $[0, 1]$, orthonormal in $L^2[0, 1]$ (that is,
$\int_0^1 \varphi_n \varphi_m \, dt$ is $1$ if $n = m$ and $0$ otherwise) and satisfy
$|\varphi_n(t)| \le M$ for all $n$ and all $t \in [0, 1]$, there is a sequence
$(\psi_n)_{n \in \mathbb{N}}$ of functions $\mathbb{R} \to \mathbb{R}$, almost everywhere
measurable on $[0, 1]$, orthonormal in the same sense and with $|\psi_n(t)| \le M$ for all $n$
and all $t \in [0, 1]$, such that every $\varphi_n$ equals some $\psi_m$ and $(\psi_n)$ is
complete: every $g \in L^2[0, 1]$ with $\int_0^1 \psi_n g \, dt = 0$ for all $n$ vanishes
almost everywhere on $[0, 1]$.

The case of interest in the original problem is when infinitely many functions are necessary
for the completion. -/
def ScottishBookProblem86Claim : Prop :=
  ∀ (M : ℝ) (φ : ℕ → ℝ → ℝ), 0 < M →
    (∀ n, AEStronglyMeasurable (φ n) scottishBook86Measure) →
    (∀ n m, ∫ t, φ n t * φ m t ∂scottishBook86Measure =
      if n = m then 1 else 0) →
    (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |φ n t| ≤ M) →
    ∃ ψ : ℕ → ℝ → ℝ,
      (∀ n, AEStronglyMeasurable (ψ n) scottishBook86Measure) ∧
      (∀ n m, ∫ t, ψ n t * ψ m t ∂scottishBook86Measure =
        if n = m then 1 else 0) ∧
      (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |ψ n t| ≤ M) ∧
      (∀ n, ∃ m, ψ m = φ n) ∧
      ∀ g : ℝ → ℝ, MemLp g 2 scottishBook86Measure →
        (∀ n, ∫ t, ψ n t * g t ∂scottishBook86Measure = 0) →
        g =ᵐ[scottishBook86Measure] 0

end

open Set
open scoped ComplexConjugate

private noncomputable abbrev start : ℝ := 1 / 8
private noncomputable abbrev period : ℝ := 1 - start

private theorem start_lt_one : start < 1 := by norm_num

private theorem period_pos : 0 < period := sub_pos.mpr start_lt_one

private theorem right_subset : Ioc start 1 ⊆ Icc (0 : ℝ) 1 :=
  fun _ hx ↦ ⟨(by norm_num : (0 : ℝ) ≤ start).trans hx.1.le, hx.2⟩

private theorem left_subset : Icc (0 : ℝ) start ⊆ Icc (0 : ℝ) 1 :=
  Icc_subset_Icc_right start_lt_one.le

private noncomputable def mode (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle period)

/-- The pair at `n` and `-n` consists of the cosine plus and minus the sine.
Using these sums gives the same normalization for every frequency, including zero. -/
private noncomputable def wave (n : ℤ) (x : ℝ) : ℝ := (mode n x).re + (mode n x).im

private noncomputable def system (n : ℤ) : ℝ → ℝ :=
  (Ioc start 1).indicator (fun x ↦ wave n x / Real.sqrt period)

private theorem continuous_mode (n : ℤ) : Continuous (mode n) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' period)

private theorem norm_mode (n : ℤ) (x : ℝ) : ‖mode n x‖ = 1 := by
  rw [mode, fourier_apply, Circle.norm_coe]

private theorem mode_add (n m : ℤ) (x : ℝ) : mode (n + m) x = mode n x * mode m x :=
  fourier_add

private theorem mode_neg (n : ℤ) (x : ℝ) : mode (-n) x = conj (mode n x) :=
  fourier_neg

private theorem measurable_system (n : ℤ) : Measurable (system n) := by
  have h := (Complex.continuous_re.comp (continuous_mode n)).add
    (Complex.continuous_im.comp (continuous_mode n))
  exact (h.div_const _).measurable.indicator measurableSet_Ioc

private theorem abs_system_le (n : ℤ) (x : ℝ) : |system n x| ≤ 2 := by
  have hs : 0 < Real.sqrt period := Real.sqrt_pos.2 period_pos
  by_cases hx : x ∈ Ioc start 1
  · rw [system, indicator_of_mem hx, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have hnorm := Complex.normSq_eq_norm_sq (mode n x)
    rw [norm_mode, Complex.normSq_apply] at hnorm
    have hsq : |wave n x| ^ 2 ≤ 2 := by
      rw [sq_abs, wave]
      nlinarith [sq_nonneg ((mode n x).re - (mode n x).im)]
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    calc
      _ ≤ 2 := hsq
      _ ≤ _ := by rw [mul_pow, Real.sq_sqrt period_pos.le]; norm_num [period, start]
  · rw [system, indicator_of_notMem hx, abs_zero]
    norm_num

private theorem integrable_mode (n : ℤ) : Integrable (mode n) (volume.restrict (Ioc start 1)) :=
  (MemLp.of_bound (p := 1) (continuous_mode n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x ↦ (norm_mode n x).le)).integrable (by norm_num)

private theorem integral_mode (n : ℤ) :
    (∫ x in Ioc start 1, mode n x) = if n = 0 then (period : ℂ) else 0 := by
  let : Fact (0 < period) := ⟨period_pos⟩
  have h := congrFun (fourierCoeff_fourier (T := period) n) (0 : ℤ)
  have hEnd : start + period = 1 := by ring
  rw [fourierCoeff_eq_intervalIntegral _ _ start, hEnd,
    intervalIntegral.integral_of_le start_lt_one.le] at h
  simp only [neg_zero, fourier_zero, one_smul, Pi.single_apply] at h
  change (1 / period) • (∫ x in Ioc start 1, mode n x) = (if 0 = n then 1 else 0) at h
  have h' := congrArg (fun z : ℂ ↦ period • z) h
  change period • ((1 / period) • (∫ x in Ioc start 1, mode n x)) =
    period • (if 0 = n then (1 : ℂ) else 0) at h'
  rw [smul_smul, mul_one_div_cancel period_pos.ne', one_smul] at h'
  by_cases hn : n = 0 <;> simpa [hn, eq_comm, Complex.real_smul] using h'

private theorem integral_wave_mul (n m : ℤ) :
    (∫ x in Ioc start 1, wave n x * wave m x) = if n = m then period else 0 := by
  have hfun : (fun x ↦ wave n x * wave m x) =
      fun x ↦ (mode (n + -m) x).re + (mode (n + m) x).im := by
    funext x
    rw [mode_add, mode_add, mode_neg]
    simp only [wave, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hn : Integrable (fun x ↦ (mode (n + -m) x).re) (volume.restrict (Ioc start 1)) :=
    (integrable_mode _).re
  have hm : Integrable (fun x ↦ (mode (n + m) x).im) (volume.restrict (Ioc start 1)) :=
    (integrable_mode _).im
  have hre : (∫ x in Ioc start 1, (mode (n + -m) x).re) =
      (∫ x in Ioc start 1, mode (n + -m) x).re := integral_re (integrable_mode _)
  have him : (∫ x in Ioc start 1, (mode (n + m) x).im) =
      (∫ x in Ioc start 1, mode (n + m) x).im := integral_im (integrable_mode _)
  rw [hfun, integral_add hn hm, hre, him, integral_mode, integral_mode]
  have hnm : n + -m = 0 ↔ n = m := by omega
  simp only [hnm]
  split_ifs <;> simp

private theorem integral_system_mul (n : ℤ) (g : ℝ → ℝ) :
    (∫ x, system n x * g x ∂scottishBook86Measure) =
      (∫ x in Ioc start 1, wave n x * g x) / Real.sqrt period := by
  have hfun : (fun x ↦ system n x * g x) =
      (Ioc start 1).indicator (fun x ↦ (wave n x * g x) / Real.sqrt period) := by
    funext x
    by_cases hx : x ∈ Ioc start 1
    · rw [system, indicator_of_mem hx, indicator_of_mem hx, div_mul_eq_mul_div]
    · rw [system, indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  rw [hfun, integral_indicator measurableSet_Ioc]
  change (∫ x in Ioc start 1, (wave n x * g x) / Real.sqrt period
    ∂(volume.restrict (Icc (0 : ℝ) 1))) = _
  rw [Measure.restrict_restrict_of_subset right_subset, integral_div]

private theorem integral_system_system (n m : ℤ) :
    (∫ x, system n x * system m x ∂scottishBook86Measure) = if n = m then 1 else 0 := by
  have h : (∫ x in Ioc start 1, wave n x * system m x) =
      ∫ x in Ioc start 1, (wave n x * wave m x) / Real.sqrt period := by
    exact setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by
      rw [system, indicator_of_mem hx, mul_div_assoc]
  rw [integral_system_mul, h, integral_div, div_div, ← pow_two,
    Real.sq_sqrt period_pos.le, integral_wave_mul]
  split_ifs <;> simp [period_pos.ne']

private theorem measure_split : scottishBook86Measure =
    volume.restrict (Icc (0 : ℝ) start) + volume.restrict (Ioc start 1) := by
  change volume.restrict (Icc (0 : ℝ) 1) = _
  rw [← Icc_union_Ioc_eq_Icc (by norm_num : (0 : ℝ) ≤ start) start_lt_one.le,
    Measure.restrict_union _ measurableSet_Ioc]
  exact disjoint_left.mpr fun _ hx hy ↦ (not_lt_of_ge hx.2) hy.1

private theorem integral_sq_right_eq_zero {g : ℝ → ℝ}
    (hL2 : MemLp g 2 (volume.restrict (Ioc start 1)))
    (hwave : ∀ n : ℤ, (∫ x in Ioc start 1, wave n x * g x) = 0) :
    (∫ x in Ioc start 1, g x ^ 2) = 0 := by
  have hc : MemLp (fun x ↦ (g x : ℂ)) 2 (volume.restrict (Ioc start 1)) := hL2.ofReal
  have hcoeff (k : ℤ) : fourierCoeffOn start_lt_one (fun x ↦ (g x : ℂ)) k = 0 := by
    let F : ℝ → ℂ := fun x ↦ mode (-k) x * (g x : ℂ)
    have hF : Integrable F (volume.restrict (Ioc start 1)) := by
      have hm := (continuous_mode (-k)).aestronglyMeasurable (μ := volume.restrict (Ioc start 1))
      have hmode : MemLp (mode (-k)) 2 (volume.restrict (Ioc start 1)) :=
        MemLp.of_bound hm 1 (Filter.Eventually.of_forall fun x ↦ (norm_mode (-k) x).le)
      exact hmode.integrable_mul hc
    have hRe : Integrable (fun x ↦ (F x).re) (volume.restrict (Ioc start 1)) := hF.re
    have hIm : Integrable (fun x ↦ (F x).im) (volume.restrict (Ioc start 1)) := hF.im
    have intRe : (∫ x in Ioc start 1, (F x).re) = (∫ x in Ioc start 1, F x).re :=
      integral_re hF
    have intIm : (∫ x in Ioc start 1, (F x).im) = (∫ x in Ioc start 1, F x).im :=
      integral_im hF
    -- Orthogonality against the two opposite frequencies kills both coordinates.
    have hplus : (∫ x in Ioc start 1, (F x).re + (F x).im) = 0 := by
      convert hwave (-k) using 1
      congr 1
      funext x
      simp [F, wave, Complex.mul_re, Complex.mul_im, add_mul]
    have hminus : (∫ x in Ioc start 1, (F x).re - (F x).im) = 0 := by
      convert hwave k using 1
      congr 1
      funext x
      simp [F, wave, mode_neg, Complex.mul_re, Complex.mul_im, add_mul, sub_eq_add_neg]
    rw [integral_add hRe hIm, intRe, intIm] at hplus
    rw [integral_sub hRe hIm, intRe, intIm] at hminus
    have hzero : (∫ x in Ioc start 1, F x) = 0 := by
      apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
    rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le start_lt_one.le]
    change (1 / period) • (∫ x in Ioc start 1, F x) = 0
    rw [hzero, smul_zero]
  have hs : HasSum (fun _ : ℤ ↦ (0 : ℝ))
      (period⁻¹ • ∫ x in Ioc start 1, g x ^ 2) := by
    simpa only [hcoeff, norm_zero, pow_two, zero_mul,
      intervalIntegral.integral_of_le start_lt_one.le,
      Complex.norm_real, Real.norm_eq_abs, abs_mul_abs_self] using
      hasSum_sq_fourierCoeffOn start_lt_one hc
  exact (smul_eq_zero.mp (hs.unique hasSum_zero)).resolve_left (inv_ne_zero period_pos.ne')

private theorem integral_sq_lt_one {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g scottishBook86Measure)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ 2)
    (ho : ∀ n : ℤ, (∫ x, system n x * g x ∂scottishBook86Measure) = 0) :
    (∫ x, g x ^ 2 ∂scottishBook86Measure) < 1 := by
  have hR := Measure.restrict_mono right_subset (le_rfl : (volume : Measure ℝ) ≤ volume)
  have hL := Measure.restrict_mono left_subset (le_rfl : (volume : Measure ℝ) ≤ volume)
  have hbound : ∀ᵐ x ∂scottishBook86Measure, ‖g x‖ ≤ 2 :=
    (ae_restrict_mem measurableSet_Icc).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using hb x hx
  let : IsFiniteMeasure scottishBook86Measure := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hLp : MemLp g 2 scottishBook86Measure := MemLp.of_bound hg 2 hbound
  have hright := integral_sq_right_eq_zero (hLp.mono_measure hR) fun n ↦ by
    have hn := ho n
    rw [integral_system_mul] at hn
    exact (div_eq_zero_iff.mp hn).resolve_right (Real.sqrt_ne_zero'.2 period_pos)
  have hleft : (∫ x in Icc (0 : ℝ) start, g x ^ 2) ≤ 1 / 2 := by
    calc
      _ ≤ ∫ _ in Icc (0 : ℝ) start, (4 : ℝ) := by
        apply integral_mono_ae (hLp.mono_measure hL).integrable_sq (integrable_const _)
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := 0) (b := start))]
          with x hx
        have h := (sq_le_sq₀ (abs_nonneg (g x)) (by norm_num)).2 (hb x (left_subset hx))
        simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Icc]
        norm_num [start]
  rw [measure_split, integral_add_measure (hLp.mono_measure hL).integrable_sq
    (hLp.mono_measure hR).integrable_sq, hright, add_zero]
  linarith

/--
**Banach's Scottish Book Problem 86 fails.** The Scottish Book Problem 86 claim is false: there
are a real $M > 0$ and a sequence $(\varphi_n)_{n \in \mathbb{N}}$ of functions
$\mathbb{R} \to \mathbb{R}$, almost everywhere measurable on $[0, 1]$, orthonormal in
$L^2[0, 1]$ and with $|\varphi_n(t)| \le M$ for all $n$ and all $t \in [0, 1]$, such that there
is no sequence $(\psi_n)_{n \in \mathbb{N}}$ of functions $\mathbb{R} \to \mathbb{R}$, almost
everywhere measurable on $[0, 1]$, orthonormal in $L^2[0, 1]$ and with $|\psi_n(t)| \le M$ for
all $n$ and all $t \in [0, 1]$, that has every $\varphi_n$ as one of its terms and is complete:
every $g \in L^2[0, 1]$ with $\int_0^1 \psi_n g \, dt = 0$ for all $n$ vanishes almost
everywhere on $[0, 1]$.

Source:
S. Banach, Problem 86 of the Scottish Book; negative answer via
A. Plichko and A. Razenkov, "On three problems from the Scottish Book
connected with orthogonal systems", Colloq. Math. 70 (1996), 227–234,
Proposition 3, which constructs a bounded orthogonal sequence in a
Banach space densely and non-compactly embedded in a Hilbert space
that admits no extension to a fundamental orthogonal sequence using
elements of the Banach space. Earlier work on the problem includes
S. Kaczmarz (1936) and K. S. Kazarian ("On a problem of S. Banach
from the Scottish Book", Proc. Amer. Math. Soc. 110 (1990), 881–887).
-/
public theorem banach86_refuted : ¬ ScottishBookProblem86Claim := by
  intro h
  let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  obtain ⟨ψ, hmeas, horth, hbound, hcontains, hcomplete⟩ :=
    h 2 (fun n ↦ system (e n)) (by norm_num)
      (fun n ↦ (measurable_system (e n)).aestronglyMeasurable)
      (fun n m ↦ by simp only [integral_system_system, e.apply_eq_iff_eq])
      (fun n x _ ↦ abs_system_le (e n) x)
  have horiginal (m : ℕ) : ∃ n : ℤ, ψ m = system n := by
    by_contra! hnew
    have ho (n : ℤ) : (∫ x, system n x * ψ m x ∂scottishBook86Measure) = 0 := by
      obtain ⟨j, hj⟩ := hcontains (e.symm n)
      rw [e.apply_symm_apply] at hj
      rw [← hj, horth, ite_eq_right]
      rintro rfl
      exact hnew n hj
    have hsmall := integral_sq_lt_one (hmeas m) (hbound m) ho
    have hunit : (∫ x, ψ m x ^ 2 ∂scottishBook86Measure) = 1 := by
      simpa [pow_two] using horth m m
    rw [hunit] at hsmall
    exact (lt_irrefl 1) hsmall
  let g : ℝ → ℝ := (Icc (0 : ℝ) start).indicator (fun _ ↦ 1)
  let : IsFiniteMeasure scottishBook86Measure := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hg : MemLp g 2 scottishBook86Measure :=
    (memLp_const 1).indicator measurableSet_Icc.nullMeasurableSet
  have hgzero := hcomplete g hg fun m ↦ by
    obtain ⟨n, hn⟩ := horiginal m
    rw [hn, integral_system_mul]
    have hz : (∫ x in Ioc start 1, wave n x * g x) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
      have hx' : x ∉ Icc (0 : ℝ) start := fun hy ↦ (not_lt_of_ge hy.2) hx.1
      dsimp only [g]
      rw [indicator_of_notMem hx', mul_zero, Pi.zero_apply]
    rw [hz, zero_div]
  have hnull : scottishBook86Measure (Icc (0 : ℝ) start) = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hgzero
    refine measure_mono_null (fun x hx ↦ ?_) hgzero
    change (Icc (0 : ℝ) start).indicator (fun _ ↦ (1 : ℝ)) x ≠ 0
    rw [indicator_of_mem hx]
    exact one_ne_zero
  change volume.restrict (Icc (0 : ℝ) 1) (Icc 0 start) = 0 at hnull
  rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr left_subset,
    Real.volume_Icc, sub_zero] at hnull
  exact (ENNReal.ofReal_pos.mpr (by norm_num : 0 < start)).ne' hnull

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted
