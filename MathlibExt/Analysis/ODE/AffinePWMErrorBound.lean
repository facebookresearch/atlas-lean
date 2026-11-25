/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.GronwallIntegral
public import MathlibExt.Analysis.ODE.PWMPrimitiveBound
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Switched-to-averaged error bound for affine PWM systems

Let `A` be a bounded linear operator on a finite-dimensional real normed space `E`, let `b ∈ E`
be a constant input direction and let `c` be a common forcing. The switched
trajectory `x` solves `x' = A x + s(t) • b + c(t)`, where `s = pwmSignal ε d` is the
pulse-width signal with switching-cycle length `ε` and duty `d`, and the averaged trajectory
`y` solves `y' = A y + d(t) • b + c(t)`; both are given in integral-equation form on `[0, T]`.

In the difference of the two equations the forcing `c` cancels and, since `b` is constant, the
input contributes `q(t) • b`, where `q(t) = ∫₀ᵗ (s - d)` is the discrepancy primitive. A bound
`|q| ≤ Q` therefore reduces the error to the integral Gronwall inequality
`le_mul_exp_of_le_add_integral`, and `abs_pwmPrimitive_le` supplies `Q = ε (1 + Ld T / 2)`.

## Main results

* `norm_sub_le_exp_mul_of_primitive_le`: if `|q| ≤ Q` on `[0, T]` and both integrands are
  interval integrable, then `‖x t - y t‖ ≤ exp(‖A‖ T) (‖x₀ - y₀‖ + ‖b‖ Q)` there.
* `norm_sub_le_of_primitive_le_zeroOperator`: at `A = 0` the exponential factor is `1`.
* `switched_averaged_error_le`: for a continuous forcing `c` and an `Ld`-Lipschitz duty with
  values in `[0, 1]`,
  `‖x t - y t‖ ≤ exp(‖A‖ T) (‖x₀ - y₀‖ + ‖b‖ ε (1 + Ld T / 2))` on `[0, T]`.
* `switched_averaged_error_le_of_constDuty_sharp`: a constant duty `c₀ ∈ [0, 1]` gives the
  factor `c₀ (1 - c₀) ε`, at most `ε / 4` and zero at duties `0` and `1`.
* `switched_averaged_error_le_of_constDuty`: the coarser constant-duty factor `ε`.

The initial mismatch `‖x₀ - y₀‖` is kept in every bound. Only the affine case with a fixed
input direction is treated; there is no state-dependent input map, hybrid or Zeno dynamics,
stability transfer, switching loss or dead time.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace MathlibExt.Analysis.ODE.AffinePWMErrorBound

open MathlibExt.Analysis.ODE.PWMPrimitiveBound

/-- A function equal to `z₀` plus the primitive of an interval-integrable `f` on `[0, T]` is
continuous there. -/
private theorem continuousOn_of_eq_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {z f : ℝ → E} {z₀ : E} {T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T)
    (hz : ∀ t ∈ Icc 0 T, z t = z₀ + ∫ u in (0 : ℝ)..t, f u) :
    ContinuousOn z (Icc 0 T) := by
  have := intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
  rw [uIcc_of_le hT] at this
  exact (continuousOn_const.add this).congr fun t ht => hz t ht

/-- If `z t = z₀ + ∫₀ᵗ (A (z u) + p u + c u)` on `[0, T]` with `p` interval integrable and `c`
continuous, then the integrand is interval integrable on `[0, T]`. The integral equation alone
does not say so, since a non-integrable integrand has integral `0`: let `t*` be the supremum of
the times up to which it is integrable. Gronwall bounds `z` before `t*`, so the integrand is
integrable up to `t*`; past `t*` every integral vanishes, `z` is constant and the integrand is
integrable again, so `t* = T`. -/
private theorem intervalIntegrable_of_eq_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (c : ℝ → E) (hc : Continuous c)
    {T : ℝ} (hT : 0 ≤ T) (p : ℝ → E) (hp : IntervalIntegrable p volume 0 T) (z : ℝ → E)
    (z₀ : E) (hz : ∀ t ∈ Icc 0 T, z t = z₀ + ∫ u in (0 : ℝ)..t, (A (z u) + p u + c u)) :
    IntervalIntegrable (fun u => A (z u) + p u + c u) volume 0 T := by
  set f : ℝ → E := fun u => A (z u) + p u + c u with hf
  have hpc : IntervalIntegrable (fun u => p u + c u) volume 0 T :=
    hp.add (hc.intervalIntegrable _ _)
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ T → uIcc a b ⊆ uIcc 0 T :=
    fun ha hab hb => by
      rw [uIcc_of_le hab, uIcc_of_le hT]; exact Icc_subset_Icc ha hb
  set S : Set ℝ := {t | t ∈ Icc 0 T ∧ IntervalIntegrable f volume 0 t} with hS
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT⟩, IntervalIntegrable.refl⟩
  have hSbdd : BddAbove S := ⟨T, fun t ht => ht.1.2⟩
  set ts := sSup S with hts
  have hts0 : 0 ≤ ts := le_csSup hSbdd hS0
  have htsT : ts ≤ T := csSup_le ⟨0, hS0⟩ fun t ht => ht.1.2
  have hcontS : ∀ t' ∈ S, ContinuousOn z (Icc 0 t') := fun t' ht' =>
    continuousOn_of_eq_add_integral ht'.1.1 ht'.2 fun t ht => hz t ⟨ht.1, ht.2.trans ht'.1.2⟩
  set P : ℝ := ∫ u in (0 : ℝ)..T, ‖p u + c u‖ with hP_def
  have hP : 0 ≤ P := intervalIntegral.integral_nonneg hT fun _ _ => norm_nonneg _
  set B : ℝ := (‖z₀‖ + P) * Real.exp (‖A‖ * T) with hB
  have hboundS : ∀ t' ∈ S, ∀ t ∈ Icc 0 t', ‖z t‖ ≤ B := by
    intro t' ht'
    have hzc := hcontS t' ht'
    have key : ∀ t ∈ Icc 0 t', ‖z t‖ ≤ (‖z₀‖ + P) + ‖A‖ * ∫ r in (0 : ℝ)..t, ‖z r‖ := by
      intro t ht
      have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans ht'.1.2⟩
      have hfi : IntervalIntegrable f volume 0 t := ht'.2.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le ht'.1.1]; exact Icc_subset_Icc le_rfl ht.2)
      have hzn : IntervalIntegrable (fun r => ‖z r‖) volume 0 t :=
        ((continuous_norm.comp_continuousOn hzc).mono (by
          rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
      have hpcn : IntervalIntegrable (fun r => ‖p r + c r‖) volume 0 t :=
        hpc.norm.mono_set (hsub le_rfl ht.1 htT.2)
      have hPt : ∫ u in (0 : ℝ)..t, ‖p u + c u‖ ≤ P :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 htT.2
          (ae_of_all _ fun _ => norm_nonneg _) hpc.norm
      have hI : ∫ u in (0 : ℝ)..t, ‖f u‖ ≤
          ∫ u in (0 : ℝ)..t, (‖A‖ * ‖z u‖ + ‖p u + c u‖) :=
        intervalIntegral.integral_mono_on ht.1 hfi.norm ((hzn.const_mul _).add hpcn)
          fun r _ => by
            simp only [hf, add_assoc]
            exact (norm_add_le _ _).trans (by gcongr; exact A.le_opNorm _)
      rw [intervalIntegral.integral_add (hzn.const_mul _) hpcn,
        intervalIntegral.integral_const_mul] at hI
      have hN := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) ht.1
      rw [hz t htT]
      calc ‖z₀ + ∫ u in (0 : ℝ)..t, f u‖ ≤ ‖z₀‖ + ‖∫ u in (0 : ℝ)..t, f u‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    intro t ht
    have h1 := le_mul_exp_of_le_add_integral (u := fun r => ‖z r‖) (norm_nonneg _)
      ((continuous_norm.comp_continuousOn hzc).integrableOn_Icc) (fun _ _ => norm_nonneg _)
      key t ht
    refine h1.trans ?_
    rw [hB]
    gcongr
    exact ht.2.trans ht'.1.2
  have hcontIoo : ContinuousOn z (Ioo 0 ts) := fun u hu => by
    obtain ⟨t', ht'S, hut'⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ hu.2
    exact ((hcontS t' ht'S).continuousAt (Icc_mem_nhds hu.1 hut')).continuousWithinAt
  have hbIoo : ∀ u ∈ Ioo 0 ts, ‖A (z u)‖ ≤ ‖A‖ * B := fun u hu => by
    obtain ⟨t', ht'S, hut'⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ hu.2
    exact (A.le_opNorm _).trans (by gcongr; exact hboundS t' ht'S u ⟨hu.1.le, hut'.le⟩)
  have hAz : IntervalIntegrable (fun u => A (z u)) volume 0 ts := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hts0]
    exact IntegrableOn.of_bound measure_Ioo_lt_top
      ((A.continuous.comp_continuousOn hcontIoo).aestronglyMeasurable measurableSet_Ioo)
      (‖A‖ * B) ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hbIoo))
  have hfeq : (fun u => A (z u) + (p u + c u)) = f := by
    funext u; simp only [hf, add_assoc]
  have hts_mem : ts ∈ S := ⟨⟨hts0, htsT⟩, by
    rw [← hfeq]; exact hAz.add (hpc.mono_set (hsub le_rfl hts0 htsT))⟩
  have hts_eq : ts = T := by
    by_contra hne
    have hlt : ts < T := lt_of_le_of_ne htsT hne
    have hconst : ∀ u ∈ Ioc ts T, z u = z₀ := fun u hu => by
      have hnot : u ∉ S := notMem_of_csSup_lt hu.1 hSbdd
      have hni : ¬ IntervalIntegrable f volume 0 u := fun hi =>
        hnot ⟨⟨hts0.trans hu.1.le, hu.2⟩, hi⟩
      rw [hz u ⟨hts0.trans hu.1.le, hu.2⟩, intervalIntegral.integral_undef hni, add_zero]
    have h1 : IntervalIntegrable (fun u => A z₀ + (p u + c u)) volume ts T :=
      intervalIntegrable_const.add (hpc.mono_set (hsub hts0 hlt.le le_rfl))
    have htail : IntervalIntegrable f volume ts T := by
      refine (intervalIntegrable_congr ?_).mp h1
      intro u hu
      rw [uIoc_of_le hlt.le] at hu
      simp only [hf, hconst u hu, add_assoc]
    have hT_mem : T ∈ S := ⟨⟨hT, le_rfl⟩, hts_mem.2.trans htail⟩
    exact hne (le_antisymm htsT (le_csSup hSbdd hT_mem))
  rw [← hts_eq]; exact hts_mem.2

/-- Bounded-primitive error estimate, split from the affine
specialization: if the switched and averaged trajectories satisfy
their integral equations on `[0, T]` with integrable integrands and a
common forcing `c`, and the discrepancy primitive is bounded
by `Q` on `[0, T]`, then
the trajectory error is at most
`exp(‖A‖ T) (‖x₀ - y₀‖ + ‖b‖ Q)` on `[0, T]`. -/
theorem norm_sub_le_exp_mul_of_primitive_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (b : E) (c : ℝ → E)
    (T Q : ℝ) (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (s d : ℝ → ℝ) (x y : ℝ → E) (x₀ y₀ : E)
    (hx : ∀ t ∈ Set.Icc 0 T, x t = x₀ +
      ∫ u in (0 : ℝ)..t, (A (x u) + (s u) • b + c u))
    (hy : ∀ t ∈ Set.Icc 0 T, y t = y₀ +
      ∫ u in (0 : ℝ)..t, (A (y u) + (d u) • b + c u))
    (hxi : IntervalIntegrable (fun u => A (x u) + (s u) • b + c u) volume 0 T)
    (hyi : IntervalIntegrable (fun u => A (y u) + (d u) • b + c u) volume 0 T)
    (hq : ∀ t ∈ Set.Icc 0 T, |∫ u in (0 : ℝ)..t, (s u - d u)| ≤ Q)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - y t‖ ≤ Real.exp (‖A‖ * T) * (‖x₀ - y₀‖ + ‖b‖ * Q) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hec : ContinuousOn (fun r => x r - y r) (Icc 0 T) :=
    (continuousOn_of_eq_add_integral hT hxi hx).sub (continuousOn_of_eq_add_integral hT hyi hy)
  have key : ∀ t ∈ Icc 0 T,
      ‖x t - y t‖ ≤ (‖x₀ - y₀‖ + ‖b‖ * Q) + ‖A‖ * ∫ r in (0 : ℝ)..t, ‖x r - y r‖ := by
    intro t ht
    have hsT : uIcc 0 t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2
    have hfxt := hxi.mono_set hsT
    have hfyt := hyi.mono_set hsT
    have hect : ContinuousOn (fun r => x r - y r) (uIcc 0 t) :=
      hec.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
    have hAe : IntervalIntegrable (fun u => A (x u - y u)) volume 0 t :=
      (A.continuous.comp_continuousOn hect).intervalIntegrable
    have hen : IntervalIntegrable (fun u => ‖x u - y u‖) volume 0 t :=
      (continuous_norm.comp_continuousOn hect).intervalIntegrable
    have hfun : (fun u => (s u - d u) • b) = fun u =>
        (A (x u) + s u • b + c u) - (A (y u) + d u • b + c u) - A (x u - y u) := by
      funext u; simp only [map_sub, sub_smul]; abel
    have hsd : IntervalIntegrable (fun u => (s u - d u) • b) volume 0 t := by
      rw [hfun]; exact (hfxt.sub hfyt).sub hAe
    have heq : x t - y t = (x₀ - y₀) + ((∫ u in (0 : ℝ)..t, A (x u - y u)) +
        (∫ u in (0 : ℝ)..t, (s u - d u)) • b) := by
      rw [hx t ht, hy t ht, ← intervalIntegral.integral_smul_const,
        ← intervalIntegral.integral_add hAe hsd]
      have : ∫ u in (0 : ℝ)..t, (A (x u - y u) + (s u - d u) • b) =
          (∫ u in (0 : ℝ)..t, (A (x u) + s u • b + c u)) -
            ∫ u in (0 : ℝ)..t, (A (y u) + d u • b + c u) := by
        rw [← intervalIntegral.integral_sub hfxt hfyt]
        congr 1; funext u; simp only [map_sub, sub_smul]; abel
      rw [this]; abel
    have hI : ‖∫ u in (0 : ℝ)..t, A (x u - y u)‖ ≤
        ‖A‖ * ∫ r in (0 : ℝ)..t, ‖x r - y r‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on ht.1 hAe.norm (hen.const_mul _)
        fun r _ => A.le_opNorm _
    have hqt := hq t ht
    rw [heq]
    calc ‖(x₀ - y₀) + ((∫ u in (0 : ℝ)..t, A (x u - y u)) +
          (∫ u in (0 : ℝ)..t, (s u - d u)) • b)‖
        ≤ ‖x₀ - y₀‖ + (‖∫ u in (0 : ℝ)..t, A (x u - y u)‖ +
          |∫ u in (0 : ℝ)..t, (s u - d u)| * ‖b‖) := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [norm_nonneg b]
  have h1 := le_mul_exp_of_le_add_integral (u := fun r => ‖x r - y r‖) (norm_nonneg _)
    ((continuous_norm.comp_continuousOn hec).integrableOn_Icc) (fun _ _ => norm_nonneg _)
    key t ht
  refine h1.trans ?_
  have hexp : Real.exp (‖A‖ * t) ≤ Real.exp (‖A‖ * T) := by
    gcongr; exact ht.2
  have hnn : 0 ≤ ‖x₀ - y₀‖ + ‖b‖ * Q := by positivity
  calc (‖x₀ - y₀‖ + ‖b‖ * Q) * Real.exp (‖A‖ * t)
      ≤ (‖x₀ - y₀‖ + ‖b‖ * Q) * Real.exp (‖A‖ * T) := mul_le_mul_of_nonneg_left hexp hnn
    _ = Real.exp (‖A‖ * T) * (‖x₀ - y₀‖ + ‖b‖ * Q) := by ring

/-- The bounded-primitive estimate at zero operator: with `A = 0` the
exponential factor is `1`, so the error is the initial mismatch plus
`‖b‖ Q`; the initial mismatch is not dropped. -/
theorem norm_sub_le_of_primitive_le_zeroOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : E) (c : ℝ → E)
    (T Q : ℝ) (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (s d : ℝ → ℝ) (x y : ℝ → E) (x₀ y₀ : E)
    (hx : ∀ t ∈ Set.Icc 0 T, x t = x₀ +
      ∫ u in (0 : ℝ)..t, ((0 : E →L[ℝ] E) (x u) + (s u) • b + c u))
    (hy : ∀ t ∈ Set.Icc 0 T, y t = y₀ +
      ∫ u in (0 : ℝ)..t, ((0 : E →L[ℝ] E) (y u) + (d u) • b + c u))
    (hxi : IntervalIntegrable (fun u => (0 : E →L[ℝ] E) (x u) + (s u) • b + c u) volume 0 T)
    (hyi : IntervalIntegrable (fun u => (0 : E →L[ℝ] E) (y u) + (d u) • b + c u) volume 0 T)
    (hq : ∀ t ∈ Set.Icc 0 T, |∫ u in (0 : ℝ)..t, (s u - d u)| ≤ Q)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - y t‖ ≤ ‖x₀ - y₀‖ + ‖b‖ * Q := by
  simpa using norm_sub_le_exp_mul_of_primitive_le 0 b c T Q hT hQ s d x y x₀ y₀
    hx hy hxi hyi hq t ht

/-- Switched-to-averaged error bound: for `x' = A x + s(t) • b + c(t)`
and `y' = A y + d(t) • b + c(t)` in integral-equation form on
`[0, T]`, with `s` the pulse-width signal with switching-cycle length `ε` and duty `d`,
`‖x t - y t‖ ≤ exp(‖A‖ T) (‖x₀ - y₀‖ + ‖b‖ ε (1 + Ld T / 2))`
for every `t ∈ [0, T]`. -/
theorem switched_averaged_error_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (b : E) (c : ℝ → E) (hc : Continuous c)
    (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ) (hT : 0 ≤ T) (hε : 0 < ε)
    (hd : ∀ t ∈ Set.Icc 0 T, d t ∈ Set.Icc 0 1)
    (hLip : LipschitzOnWith Ld d (Set.Icc 0 T))
    (x y : ℝ → E) (x₀ y₀ : E)
    (hx : ∀ t ∈ Set.Icc 0 T, x t = x₀ +
      ∫ u in (0 : ℝ)..t, (A (x u) + (pwmSignal ε d u) • b + c u))
    (hy : ∀ t ∈ Set.Icc 0 T, y t = y₀ +
      ∫ u in (0 : ℝ)..t, (A (y u) + (d u) • b + c u))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - y t‖ ≤ Real.exp (‖A‖ * T) * (‖x₀ - y₀‖ + ‖b‖ * ε * (1 + (Ld : ℝ) * T / 2)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hsmul : ∀ {g : ℝ → ℝ}, IntervalIntegrable g volume 0 T →
      IntervalIntegrable (fun u => g u • b) volume 0 T := fun h =>
    ⟨h.1.smul_const _, h.2.smul_const _⟩
  have hdi : IntervalIntegrable d volume 0 T :=
    (hLip.continuousOn.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hxi := intervalIntegrable_of_eq_add_integral A c hc hT (fun u => pwmSignal ε d u • b)
    (hsmul (intervalIntegrable_pwmSignal ε d 0 T)) x x₀ hx
  have hyi := intervalIntegrable_of_eq_add_integral A c hc hT (fun u => d u • b)
    (hsmul hdi) y y₀ hy
  have h := norm_sub_le_exp_mul_of_primitive_le A b c T (ε * (1 + (Ld : ℝ) * T / 2)) hT
    (by positivity) (pwmSignal ε d) d x y x₀ y₀ hx hy hxi hyi
    (fun t ht => abs_pwmPrimitive_le T ε Ld d hT hε hd hLip t ht) t ht
  simpa only [mul_assoc] using h

/-- Sharp constant-duty bound: for a constant duty `c₀ ∈ [0, 1]` the discrepancy primitive
stays in `[0, c₀ (1 - c₀) ε]` (`pwmPrimitive_const_mem_Icc`), so the error is at most
`exp(‖A‖ T) (‖x₀ - y₀‖ + ‖b‖ c₀ (1 - c₀) ε)` on `[0, T]`. -/
theorem switched_averaged_error_le_of_constDuty_sharp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (b : E) (c : ℝ → E) (hc : Continuous c)
    (T ε c₀ : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) (hc₀ : c₀ ∈ Set.Icc 0 1)
    (x y : ℝ → E) (x₀ y₀ : E)
    (hx : ∀ t ∈ Set.Icc 0 T, x t = x₀ +
      ∫ u in (0 : ℝ)..t, (A (x u) + (pwmSignal ε (fun _ => c₀) u) • b + c u))
    (hy : ∀ t ∈ Set.Icc 0 T, y t = y₀ +
      ∫ u in (0 : ℝ)..t, (A (y u) + c₀ • b + c u))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - y t‖ ≤ Real.exp (‖A‖ * T) * (‖x₀ - y₀‖ + ‖b‖ * (c₀ * (1 - c₀) * ε)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hxi := intervalIntegrable_of_eq_add_integral A c hc hT
    (fun u => pwmSignal ε (fun _ => c₀) u • b)
    ⟨(intervalIntegrable_pwmSignal ε _ 0 T).1.smul_const _,
      (intervalIntegrable_pwmSignal ε _ 0 T).2.smul_const _⟩ x x₀ hx
  have hyi := intervalIntegrable_of_eq_add_integral A c hc hT (fun _ => c₀ • b)
    intervalIntegrable_const y y₀ hy
  have hQ : 0 ≤ c₀ * (1 - c₀) * ε :=
    mul_nonneg (mul_nonneg hc₀.1 (sub_nonneg.mpr hc₀.2)) hε.le
  exact norm_sub_le_exp_mul_of_primitive_le A b c T _ hT hQ
    (pwmSignal ε (fun _ => c₀)) (fun _ => c₀) x y x₀ y₀ hx hy hxi hyi
    (fun t ht => by
      have h := pwmPrimitive_const_mem_Icc ε c₀ t hε hc₀ ht.1
      exact (abs_of_nonneg h.1).trans_le h.2) t ht

/-- Constant duty specialization: a constant duty `c₀ ∈ [0, 1]` is
the `Ld = 0` case, giving the factor `ε (1 + 0 * T / 2) = ε` in the
headline bound. -/
theorem switched_averaged_error_le_of_constDuty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (b : E) (c : ℝ → E) (hc : Continuous c)
    (T ε c₀ : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) (hc₀ : c₀ ∈ Set.Icc 0 1)
    (x y : ℝ → E) (x₀ y₀ : E)
    (hx : ∀ t ∈ Set.Icc 0 T, x t = x₀ +
      ∫ u in (0 : ℝ)..t, (A (x u) + (pwmSignal ε (fun _ => c₀) u) • b + c u))
    (hy : ∀ t ∈ Set.Icc 0 T, y t = y₀ +
      ∫ u in (0 : ℝ)..t, (A (y u) + c₀ • b + c u))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - y t‖ ≤ Real.exp (‖A‖ * T) * (‖x₀ - y₀‖ + ‖b‖ * ε) := by
  refine (switched_averaged_error_le_of_constDuty_sharp A b c hc T ε c₀ hT hε hc₀ x y x₀ y₀
    hx hy t ht).trans ?_
  have hc1 : c₀ * (1 - c₀) ≤ 1 := by nlinarith [hc₀.1, hc₀.2]
  gcongr
  exact mul_le_of_le_one_left hε.le hc1

end MathlibExt.Analysis.ODE.AffinePWMErrorBound
