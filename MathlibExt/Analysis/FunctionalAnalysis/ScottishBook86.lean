/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import MathlibExt.Analysis.ODE.GreensOperator

/-!
# Banach's Scottish Book Problem 86

We give a bounded orthonormal sequence on the unit interval that has no complete
orthonormal extension with the same bound.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted

open MeasureTheory

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

open Set
open MathlibExt.Analysis.ODE.GreensOperator
open scoped ENNReal

local notation "μ₀" => scottishBook86Measure

-- The first four-fifths support the sine basis and leave a positive-measure complement.
private noncomputable abbrev leftInterval : Set ℝ := Icc 0 (4 / 5)
private noncomputable abbrev rightInterval : Set ℝ := Ioc (4 / 5) 1

local notation "μL" => (volume.restrict leftInterval)
local notation "μR" => (volume.restrict rightInterval)

private lemma left_subset_unit : leftInterval ⊆ Icc (0 : ℝ) 1 :=
  Icc_subset_Icc_right (by norm_num)

private lemma right_subset_unit : rightInterval ⊆ Icc (0 : ℝ) 1 :=
  fun _ hx => ⟨by linarith [hx.1], hx.2⟩

private lemma ae_mem_unit : ∀ᵐ x ∂μ₀, x ∈ Icc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

private lemma dilation_mem_left {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (4 / 5) * x ∈ leftInterval :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

private noncomputable def dilation : ℝ ≃ᵐ ℝ :=
  (Homeomorph.mulLeft₀ (4 / 5 : ℝ) (by norm_num)).toMeasurableEquiv

private lemma map_dilation : Measure.map dilation μ₀ = ENNReal.ofReal (5 / 4) • μL := by
  have hpre : dilation ⁻¹' leftInterval = Icc (0 : ℝ) 1 := by
    ext x
    change (4 / 5) * x ∈ leftInterval ↔ x ∈ Icc (0 : ℝ) 1
    exact ⟨fun hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩, dilation_mem_left⟩
  rw [scottishBook86Measure, ← hpre, ← dilation.restrict_map]
  change (Measure.map ((4 / 5 : ℝ) * ·) volume).restrict leftInterval = _
  rw [Real.map_volume_mul_left (by norm_num), Measure.restrict_smul]
  norm_num

private lemma integral_dilation (f : ℝ → ℝ) :
    (∫ x, f ((4 / 5) * x) ∂μ₀) = (5 / 4) * ∫ t, f t ∂μL := by
  change (∫ x, f (dilation x) ∂μ₀) = _
  rw [← integral_map_equiv dilation, map_dilation, integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]

local notation "c" => Real.sqrt (5 / 4)

private lemma scale_ne_zero : (c : ℝ) ≠ 0 := by positivity

private noncomputable def rescaledSine (n : ℕ) : ℝ → ℝ :=
  leftInterval.indicator (fun t => c * sineBasisFun (Equiv.pnatEquivNat.symm n) ((5 / 4) * t))

private lemma rescaledSine_measurable (n : ℕ) : Measurable (rescaledSine n) := by
  apply Measurable.indicator _ measurableSet_Icc
  unfold sineBasisFun
  fun_prop

private lemma abs_rescaledSine_le (n : ℕ) (t : ℝ) : |rescaledSine n t| ≤ 2 := by
  by_cases ht : t ∈ leftInterval
  · rw [rescaledSine, indicator_of_mem ht, sineBasisFun, ← mul_assoc, abs_mul,
      ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 4), abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt ((5 / 4) * 2) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)
      _ ≤ 2 := by
        rw [mul_one, Real.sqrt_le_iff]
        norm_num
  · simp [rescaledSine, indicator_of_notMem ht]

private lemma rescaledSine_dilation (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    rescaledSine n ((4 / 5) * x) = c * sineBasisFun (Equiv.pnatEquivNat.symm n) x := by
  rw [rescaledSine, indicator_of_mem (dilation_mem_left hx)]
  have : (5 / 4 : ℝ) * ((4 / 5) * x) = x := by ring
  rw [this]

private lemma integral_rescaledSine_mul (n : ℕ) (f : ℝ → ℝ) :
    (∫ x, sineBasisFun (Equiv.pnatEquivNat.symm n) x * f ((4 / 5) * x) ∂μ₀) =
      c * ∫ t, rescaledSine n t * f t ∂μ₀ := by
  let g (t : ℝ) := sineBasisFun (Equiv.pnatEquivNat.symm n) ((5 / 4) * t) * f t
  have hcomp (x : ℝ) : g ((4 / 5) * x) =
      sineBasisFun (Equiv.pnatEquivNat.symm n) x * f ((4 / 5) * x) := by
    have heq : (5 / 4 : ℝ) * ((4 / 5) * x) = x := by ring
    simp [g, heq]
  have hrestrict : Measure.restrict μ₀ leftInterval = μL := by
    rw [scottishBook86Measure, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr left_subset_unit]
  have hprod : (fun t => rescaledSine n t * f t) = leftInterval.indicator (fun t => c * g t) := by
    funext t
    by_cases ht : t ∈ leftInterval
    · simp [rescaledSine, g, ht, mul_assoc]
    · simp [rescaledSine, ht]
  simp_rw [← hcomp, integral_dilation g, hprod, integral_indicator measurableSet_Icc,
    hrestrict, integral_const_mul, ← mul_assoc]
  rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]

private lemma integral_rescaledSine_product (n m : ℕ) :
    (∫ t, rescaledSine n t * rescaledSine m t ∂μ₀) = if n = m then 1 else 0 := by
  apply mul_left_cancel₀ scale_ne_zero
  rw [← integral_rescaledSine_mul]
  calc
    _ = ∫ x, c * (sineBasisFun (Equiv.pnatEquivNat.symm n) x *
        sineBasisFun (Equiv.pnatEquivNat.symm m) x) ∂μ₀ := by
      apply integral_congr_ae
      filter_upwards [ae_mem_unit] with x hx
      rw [rescaledSine_dilation m hx]
      ring
    _ = _ := by
      rw [integral_const_mul, scottishBook86Measure, ← Measure.restrict_congr_set Ioc_ae_eq_Icc,
        ← intervalIntegral.integral_of_le zero_le_one, sine_product_integral]
      simp

private lemma integral_sq_left_eq_zero {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ₀)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ 2)
    (horth : ∀ n, (∫ t, rescaledSine n t * f t ∂μ₀) = 0) :
    (∫ t, f t ^ 2 ∂μL) = 0 := by
  have hq : QuasiMeasurePreserving dilation μ₀ μL := by
    refine ⟨dilation.measurable.aemeasurable, ?_⟩
    rw [map_dilation]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  have hL : μL ≤ μ₀ :=
    Measure.restrict_mono left_subset_unit le_rfl
  let F (x : ℝ) := f (dilation x)
  have hF : MemLp F 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
    change MemLp F 2 μ₀
    have : IsFiniteMeasure μ₀ :=
      isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
    refine MemLp.of_bound ((hf.mono_measure hL).comp_quasiMeasurePreserving hq) 2 ?_
    filter_upwards [ae_mem_unit] with x hx
    exact hb _ (left_subset_unit (dilation_mem_left hx))
  -- The restriction of `f`, pulled back to the unit interval, has all sine coefficients zero.
  have hcoeff (k : ℕ+) : inner ℝ (sineHilbertBasis k) (hF.toLp F : L2UnitInterval) = 0 := by
    rw [L2.inner_def]
    obtain ⟨n, rfl⟩ := Equiv.pnatEquivNat.symm.surjective k
    calc
      _ = ∫ x, sineBasisFun (Equiv.pnatEquivNat.symm n) x * F x ∂μ₀ := by
        apply integral_congr_ae
        filter_upwards [sineHilbertBasis_coe (Equiv.pnatEquivNat.symm n), hF.coeFn_toLp]
          with x hx hy
        rw [hx, hy, RCLike.inner_apply]
        simp [mul_comm]
      _ = 0 := by
        change (∫ x, sineBasisFun (Equiv.pnatEquivNat.symm n) x * f ((4 / 5) * x) ∂μ₀) = 0
        rw [integral_rescaledSine_mul n f, horth, mul_zero]
  have hz : (hF.toLp F : L2UnitInterval) = 0 := by
    apply sineHilbertBasis.repr.injective
    apply lp.ext
    funext k
    simpa [HilbertBasis.repr_apply_apply] using hcoeff k
  have hzero : F =ᵐ[μ₀] 0 := hF.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz)
  have hsq : (∫ x, F x ^ 2 ∂μ₀) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂μ₀ := by
        apply integral_congr_ae
        filter_upwards [hzero] with x hx
        simp [hx]
      _ = 0 := integral_zero _ _
  rw [show (fun x => F x ^ 2) = (fun x => (fun t => f t ^ 2) ((4 / 5) * x)) by rfl,
    integral_dilation (fun t => f t ^ 2)] at hsq
  exact (mul_eq_zero.mp hsq).resolve_left (by norm_num)

private lemma measure_split : μ₀ = μL + μR := by
  have hd : Disjoint leftInterval rightInterval := by
    refine disjoint_left.2 fun x hx hy => ?_
    exact not_lt_of_ge hx.2 hy.1
  rw [scottishBook86Measure, ← Icc_union_Ioc_eq_Icc (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (by norm_num : (4 / 5 : ℝ) ≤ 1), Measure.restrict_union hd measurableSet_Ioc]

private lemma measureReal_right : Measure.real μR univ = 1 / 5 := by
  rw [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Ioc]
  norm_num

private lemma no_orthogonal_unit {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ₀)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ 2)
    (horth : ∀ n, (∫ t, rescaledSine n t * f t ∂μ₀) = 0)
    (hnorm : (∫ t, f t * f t ∂μ₀) = 1) : False := by
  have : IsFiniteMeasure μ₀ :=
    isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
  have hLp : MemLp f 2 μ₀ := by
    refine MemLp.of_bound hf 2 ?_
    filter_upwards [ae_mem_unit] with x hx using hb x hx
  have hInt := hLp.integrable_norm_pow (p := 2) (by norm_num)
  simp only [Real.norm_eq_abs, sq_abs] at hInt
  rw [← show (fun t => f t ^ 2) = (fun t => f t * f t) by simp [pow_two]] at hnorm
  rw [measure_split, integral_add_measure
    (hInt.mono_measure (Measure.restrict_mono left_subset_unit le_rfl))
    (hInt.mono_measure (Measure.restrict_mono right_subset_unit le_rfl)),
    integral_sq_left_eq_zero hf hb horth, zero_add] at hnorm
  have : IsFiniteMeasure μR :=
    isFiniteMeasure_restrict.2 (by simp [Real.volume_Ioc])
  -- On the remaining fifth the square is bounded by four.
  have hle : (∫ t, f t ^ 2 ∂μR) ≤ ∫ _ : ℝ, (4 : ℝ) ∂μR := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => sq_nonneg (f t))
      (integrable_const _) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := rightInterval) measurableSet_Ioc]
      with x hx
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hb x (right_subset_unit hx))
    nlinarith [sq_le_sq' hlo hhi]
  rw [hnorm, integral_const, measureReal_right, smul_eq_mul] at hle
  norm_num at hle

private noncomputable def rightIndicator : ℝ → ℝ :=
  rightInterval.indicator (fun _ => 1)

private lemma rightIndicator_memLp : MemLp rightIndicator 2 μ₀ := by
  have : IsFiniteMeasure μ₀ :=
    isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
  exact (memLp_const (1 : ℝ)).indicator measurableSet_Ioc.nullMeasurableSet

private lemma rightIndicator_ne_zero : ¬ rightIndicator =ᵐ[μ₀] 0 := by
  intro h
  have hi : (∫ x, rightIndicator x ∂μ₀) = 0 := (integral_congr_ae h).trans (integral_zero _ _)
  have hr : Measure.restrict μ₀ rightInterval = μR := by
    rw [scottishBook86Measure, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr right_subset_unit]
  rw [rightIndicator, integral_indicator measurableSet_Ioc, hr,
    integral_const, measureReal_right, smul_eq_mul] at hi
  norm_num at hi

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
theorem banach86_refuted : ¬ ScottishBookProblem86Claim := by
  intro h
  obtain ⟨ψ, hmeas, horth, hbounded, hcontains, hcomplete⟩ :=
    h 2 rescaledSine (by norm_num) (fun n => (rescaledSine_measurable n).aestronglyMeasurable)
      integral_rescaledSine_product (fun n t _ => abs_rescaledSine_le n t)
  -- An extra term would be a bounded unit vector orthogonal to the entire sine sequence.
  have hterm (j : ℕ) : ∃ n, ψ j = rescaledSine n := by
    by_contra! hj
    apply no_orthogonal_unit (hmeas j) (hbounded j) _ (by simpa using horth j j)
    intro n
    obtain ⟨m, hm⟩ := hcontains n
    have hne : m ≠ j := by
      rintro rfl
      exact hj n hm
    simpa [hm, hne] using horth m j
  apply rightIndicator_ne_zero (hcomplete rightIndicator rightIndicator_memLp ?_)
  intro j
  obtain ⟨n, hn⟩ := hterm j
  rw [hn]
  calc
    _ = ∫ _ : ℝ, (0 : ℝ) ∂μ₀ := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ rightInterval
      · have hleft : t ∉ leftInterval := fun hmem => not_lt_of_ge hmem.2 ht.1
        simp [rescaledSine, indicator_of_notMem hleft]
      · simp [rightIndicator, indicator_of_notMem ht]
    _ = 0 := integral_zero _ _

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted
