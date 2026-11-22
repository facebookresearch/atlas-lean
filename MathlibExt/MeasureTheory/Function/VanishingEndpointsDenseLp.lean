/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Order.Basic
public import MathlibExt.Topology.ContinuousFunction.IntervalCutoff

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathlibExt.MeasureTheory.Function.VanishingEndpointsDenseLp

/-!
# Continuous functions vanishing at the endpoints are dense in `L^p ([a, b])`

For `a < b` and `1 ≤ p < ∞`, every `f ∈ L^p ([a, b])` can be approximated
arbitrarily well in `L^p` by a continuous function `g` with `g a = g b = 0`.
This strengthens Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`,
which produces a continuous approximant with compact support on `ℝ` but gives
no control over its values at the prescribed endpoints `a` and `b`: the
approximant there is cut off by a piecewise-linear "tent" factor which is `0`
at `a` and `b` and `1` away from the endpoints, and the cutoff error is sent
to `0` by dominated convergence (the error is dominated by `‖g₀‖` and
vanishes pointwise on `(a, b)`).

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean`,
`LpSpaces.continuous_vanishing_endpoints_dense_in_Lp`
(Proposition, April 6, 2021 section). The v1 formalization of this statement
is left unproved (its `report.json` entry claims it passed, but its axioms
include an extra axiom beyond the standard triple): the proof here is
original. The statement is generalized
from `ℝ`-valued functions to functions valued in a normed space over `ℝ`,
and the `1 ≤ p` hypothesis is kept, matching the book.
-/

/-- The shared clipped piecewise-linear cutoff factor, zero at `a` and `b`.
For `δ > 0`, it equals `1` on `[a + δ, b - δ]`; this plateau is nonempty
when `2 * δ ≤ b - a`. At `δ = 0`, the factor is identically zero.
This compatibility name retains the existing `L^p` API. -/
noncomputable def vanishingCutoff (a b δ : ℝ) (x : ℝ) : ℝ :=
  Real.intervalCutoff a b δ x

/-- The cutoff factor is nonnegative. -/
theorem vanishingCutoff_nonneg (a b δ : ℝ) (x : ℝ) :
    0 ≤ vanishingCutoff a b δ x :=
  Real.intervalCutoff_nonneg a b δ x

/-- The cutoff factor is at most `1`. -/
theorem vanishingCutoff_le_one (a b δ : ℝ) (x : ℝ) :
    vanishingCutoff a b δ x ≤ 1 :=
  Real.intervalCutoff_le_one a b δ x

/-- The cutoff factor is continuous. -/
theorem vanishingCutoff_continuous (a b δ : ℝ) :
    Continuous (vanishingCutoff a b δ) :=
  Real.intervalCutoff_continuous a b δ

/-- The cutoff factor vanishes at the left endpoint. -/
theorem vanishingCutoff_eq_zero_left (a b δ : ℝ) :
    vanishingCutoff a b δ a = 0 :=
  Real.intervalCutoff_eq_zero_left a b δ

/-- The cutoff factor vanishes at the right endpoint. -/
theorem vanishingCutoff_eq_zero_right (a b δ : ℝ) :
    vanishingCutoff a b δ b = 0 :=
  Real.intervalCutoff_eq_zero_right a b δ

/-- The cutoff factor equals `1` away from the endpoints. -/
theorem vanishingCutoff_eq_one (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) {x : ℝ}
    (hx1 : a + δ ≤ x) (hx2 : x ≤ b - δ) :
    vanishingCutoff a b δ x = 1 :=
  Real.intervalCutoff_eq_one a b δ x hδ hx1 hx2

section CutoffApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `n`-th cutoff approximant of `g₀`: `g₀` multiplied by the cutoff
factor with width `(b - a) / (n + 1)`. -/
noncomputable def cutoffApprox (a b : ℝ) (g₀ : ℝ → E) (n : ℕ) (x : ℝ) : E :=
  vanishingCutoff a b ((b - a) / ((n + 1 : ℕ) : ℝ)) x • g₀ x

/-- The cutoff approximant is continuous. -/
theorem cutoffApprox_continuous (a b : ℝ) (g₀ : ℝ → E) (hg₀ : Continuous g₀)
    (n : ℕ) : Continuous (cutoffApprox a b g₀ n) := by
  unfold cutoffApprox
  exact (vanishingCutoff_continuous a b _).smul hg₀

/-- The cutoff approximant vanishes at the left endpoint. -/
theorem cutoffApprox_eq_zero_left (a b : ℝ) (g₀ : ℝ → E) (n : ℕ) :
    cutoffApprox a b g₀ n a = 0 := by
  simp [cutoffApprox, vanishingCutoff_eq_zero_left]

/-- The cutoff approximant vanishes at the right endpoint. -/
theorem cutoffApprox_eq_zero_right (a b : ℝ) (g₀ : ℝ → E) (n : ℕ) :
    cutoffApprox a b g₀ n b = 0 := by
  simp [cutoffApprox, vanishingCutoff_eq_zero_right]

/-- The cutoff approximant lies in `L^p` whenever `g₀` does, for any
measure: it is pointwise dominated by `‖g₀‖` since the cutoff factor lies
in `[0, 1]`. -/
theorem cutoffApprox_memLp {p : ℝ≥0∞} {μ : Measure ℝ} {g₀ : ℝ → E}
    (hg₀ : MemLp g₀ p μ) (hg₀cont : Continuous g₀) (a b : ℝ)
    (n : ℕ) : MemLp (cutoffApprox a b g₀ n) p μ := by
  refine MemLp.of_le hg₀
    ((cutoffApprox_continuous a b g₀ hg₀cont n).aestronglyMeasurable) ?_
  filter_upwards with x
  show ‖vanishingCutoff a b ((b - a) / ((n + 1 : ℕ) : ℝ)) x • g₀ x‖ ≤ ‖g₀ x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (vanishingCutoff_nonneg _ _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (vanishingCutoff_le_one _ _ _ _)

/-- The cutoff error at a point is dominated by `‖g₀‖`. -/
theorem norm_sub_cutoffApprox_le (a b : ℝ) (g₀ : ℝ → E) (n : ℕ) (x : ℝ) :
    ‖g₀ x - cutoffApprox a b g₀ n x‖ ≤ ‖g₀ x‖ := by
  have h : g₀ x - cutoffApprox a b g₀ n x =
      (1 - vanishingCutoff a b ((b - a) / ((n + 1 : ℕ) : ℝ)) x) • g₀ x := by
    simp [cutoffApprox, sub_smul]
  have hφ0 : 0 ≤ vanishingCutoff a b ((b - a) / ((n + 1 : ℕ) : ℝ)) x :=
    vanishingCutoff_nonneg _ _ _ _
  have hφ1 : vanishingCutoff a b ((b - a) / ((n + 1 : ℕ) : ℝ)) x ≤ 1 :=
    vanishingCutoff_le_one _ _ _ _
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

end CutoffApprox

/-- **Continuous functions vanishing at the endpoints are dense in
`L^p ([a, b])`.** For `a < b`, `1 ≤ p < ∞`, `f ∈ L^p ([a, b])` and
`ε > 0`, there exists a continuous `g` with `g a = g b = 0`, `g ∈ L^p`,
and `‖f - g‖_p < ε`. -/
theorem exists_continuous_vanishing_endpoints_eLpNorm_sub_lt
    (a b : ℝ) (hab : a < b) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : MemLp f p (volume.restrict (Set.Icc a b)))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : ℝ → E, Continuous g ∧ g a = 0 ∧ g b = 0 ∧
      MemLp g p (volume.restrict (Set.Icc a b)) ∧
      eLpNorm (f - g) p (volume.restrict (Set.Icc a b)) < ε := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hp1)
  have hp0' : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 hp_top
  -- If `ε = ⊤`, the zero function works.
  by_cases hε_top : ε = ⊤
  · refine ⟨0, continuous_const, Pi.zero_apply _, Pi.zero_apply _, MemLp.zero, ?_⟩
    rw [hε_top]
    simpa using hf.eLpNorm_lt_top
  -- Otherwise, start from Mathlib's compact-support approximant `g₀`.
  have hε2 : (ε / 2) ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨g₀, -, hg₀err, hg₀cont, hg₀mem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hp_top hε2
  -- The cutoff widths tend to `0`.
  have hδ_tendsto : Tendsto (fun n : ℕ => (b - a) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)
  -- Almost every point of `[a, b]` (for the restricted measure) lies in `(a, b)`.
  have hae_Ioo : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), x ∈ Set.Ioo a b := by
    have hmeas : MeasurableSet {x : ℝ | x ∈ Set.Ioo a b} := measurableSet_Ioo
    apply (ae_restrict_iff hmeas).mpr
    rw [ae_iff]
    refine measure_mono_null (t := ({a, b} : Set ℝ)) ?_ ?_
    · intro x hx
      simp only [Set.mem_ofPred_eq, not_imp] at hx
      obtain ⟨⟨hax, hxb⟩, hxnot⟩ := hx
      rw [Set.mem_Ioo] at hxnot
      rcases not_and_or.mp hxnot with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl (le_antisymm (not_lt.mp h) hax))
      · exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr (le_antisymm hxb (not_lt.mp h))))
    · exact ((Set.countable_singleton b).insert a).measure_zero volume
  -- Dominated convergence: the cutoff errors tend to `0` in `L^p`.
  have hDCT : Tendsto
      (fun n => ∫⁻ x, ‖g₀ x - cutoffApprox a b g₀ n x‖ₑ ^ p.toReal
        ∂(volume.restrict (Set.Icc a b))) atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, Measurable
        (fun x => ‖g₀ x - cutoffApprox a b g₀ n x‖ₑ ^ p.toReal) :=
      fun n => (ENNReal.continuous_rpow_const.comp
        (continuous_enorm.comp (hg₀cont.sub (cutoffApprox_continuous a b g₀ hg₀cont n)))).measurable
    have hbound : ∀ n : ℕ, (fun x => ‖g₀ x - cutoffApprox a b g₀ n x‖ₑ ^ p.toReal)
        ≤ᵐ[volume.restrict (Set.Icc a b)] (fun x => ‖g₀ x‖ₑ ^ p.toReal) := by
      intro n
      filter_upwards with x
      exact ENNReal.rpow_le_rpow
        (enorm_le_iff_norm_le.mpr (norm_sub_cutoffApprox_le a b g₀ n x))
        p.toReal_nonneg
    have hbound_ne : (∫⁻ x, ‖g₀ x‖ₑ ^ p.toReal
        ∂(volume.restrict (Set.Icc a b))) ≠ ⊤ := by
      have hlt := hg₀mem.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top
        hg₀mem.aestronglyMeasurable] at hlt
      by_contra htop
      rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0')] at hlt
      exact (lt_irrefl (⊤ : ℝ≥0∞)) hlt
    have hlim : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
        Tendsto (fun n => ‖g₀ x - cutoffApprox a b g₀ n x‖ₑ ^ p.toReal)
          atTop (𝓝 0) := by
      filter_upwards [hae_Ioo] with x hx
      rw [Set.mem_Ioo] at hx
      have hd : (0 : ℝ) < min (x - a) (b - x) :=
        lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
      have hzero : ∀ᶠ n in atTop, g₀ x - cutoffApprox a b g₀ n x = 0 := by
        filter_upwards [hδ_tendsto.eventually (Iio_mem_nhds hd)] with n hn
        have hφ1 : vanishingCutoff a b ((b - a) / ((n + 1 : ℕ) : ℝ)) x = 1 := by
          apply vanishingCutoff_eq_one a b
            (div_pos (sub_pos.mpr hab) (by exact_mod_cast Nat.succ_pos n))
          · show a + (b - a) / ((n + 1 : ℕ) : ℝ) ≤ x
            have : (b - a) / ((n + 1 : ℕ) : ℝ) < x - a :=
              lt_of_lt_of_le hn (min_le_left _ _)
            linarith
          · show x ≤ b - (b - a) / ((n + 1 : ℕ) : ℝ)
            have : (b - a) / ((n + 1 : ℕ) : ℝ) < b - x :=
              lt_of_lt_of_le hn (min_le_right _ _)
            linarith
        simp only [cutoffApprox, hφ1, one_smul, sub_self]
      have heq : ∀ᶠ n in atTop,
          ‖g₀ x - cutoffApprox a b g₀ n x‖ₑ ^ p.toReal = 0 := by
        filter_upwards [hzero] with n hn
        rw [hn]
        simp [ENNReal.zero_rpow_of_pos hp0']
      exact (tendsto_congr' heq).mpr tendsto_const_nhds
    have h := tendsto_lintegral_of_dominated_convergence
      (fun x => ‖g₀ x‖ₑ ^ p.toReal) hmeas hbound hbound_ne hlim
    simpa using h
  -- Pick an approximant whose cutoff error is `< ε / 2`.
  have htarget_pos : (0 : ℝ≥0∞) < (ε / 2) ^ p.toReal :=
    ENNReal.rpow_pos (ENNReal.half_pos hε.ne')
      (ENNReal.div_ne_top hε_top (by norm_num))
  obtain ⟨N, hN⟩ := (hDCT.eventually (Iio_mem_nhds htarget_pos)).exists
  have hN' : (∫⁻ x, ‖g₀ x - cutoffApprox a b g₀ N x‖ₑ ^ p.toReal
      ∂(volume.restrict (Set.Icc a b))) < (ε / 2) ^ p.toReal :=
    Set.mem_Iio.mp hN
  have hdiff_lt : eLpNorm (g₀ - cutoffApprox a b g₀ N) p
      (volume.restrict (Set.Icc a b)) < ε / 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top
      (hg₀cont.sub (cutoffApprox_continuous a b g₀ hg₀cont N)).aestronglyMeasurable]
    have hpow : ((∫⁻ x, ‖(g₀ - cutoffApprox a b g₀ N) x‖ₑ ^ p.toReal
        ∂(volume.restrict (Set.Icc a b))) ^ (1 / p.toReal)) ^ p.toReal
        = ∫⁻ x, ‖(g₀ - cutoffApprox a b g₀ N) x‖ₑ ^ p.toReal
          ∂(volume.restrict (Set.Icc a b)) := by
      rw [← ENNReal.rpow_mul, div_mul_cancel₀ 1 (ne_of_gt hp0'), ENNReal.rpow_one]
    exact (ENNReal.rpow_lt_rpow_iff hp0').mp (by rw [hpow]; exact hN')
  refine ⟨cutoffApprox a b g₀ N, cutoffApprox_continuous a b g₀ hg₀cont N,
    cutoffApprox_eq_zero_left a b g₀ N, cutoffApprox_eq_zero_right a b g₀ N,
    cutoffApprox_memLp hg₀mem hg₀cont a b N, ?_⟩
  calc eLpNorm (f - cutoffApprox a b g₀ N) p (volume.restrict (Set.Icc a b))
      = eLpNorm ((f - g₀) + (g₀ - cutoffApprox a b g₀ N)) p
          (volume.restrict (Set.Icc a b)) := by rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (f - g₀) p (volume.restrict (Set.Icc a b)) +
          eLpNorm (g₀ - cutoffApprox a b g₀ N) p
            (volume.restrict (Set.Icc a b)) := eLpNorm_add_le hp1
    _ < ε / 2 + ε / 2 := by
      exact lt_of_le_of_lt (add_le_add hg₀err le_rfl)
        (ENNReal.add_lt_add_left
          (ENNReal.div_ne_top hε_top (by norm_num)) hdiff_lt)
    _ = ε := ENNReal.add_halves ε

end MathlibExt.MeasureTheory.Function.VanishingEndpointsDenseLp
