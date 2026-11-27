/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.BoundaryClassification
public import Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
public import Domains.Biology.PopulationGenetics.Diffusion.SelectionMutationSpeedMeasure
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

open MeasureTheory Set intervalIntegral
open scoped Topology
open MathlibExt.Probability.Diffusion

/-!
# Feller boundary classification of the Wright-Fisher selection-mutation diffusion

This module applies the Feller boundary predicates of
`MathlibExt.Probability.Diffusion.BoundaryClassification` (Karlin and Taylor
(1981), Chapter 15) to the Wright-Fisher selection-mutation diffusion with drift
`(θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))` and diffusion coefficient
`x * (1 - x)` (see Ewens (2004), Chapter 4). These coefficients satisfy the
standing hypotheses `IsFellerAdmissible` at every interior basepoint
(`isFellerAdmissible_selectionMutation`). With nonnegative mutation
parameters, each endpoint is exit, regular, or entrance according as the
corresponding mutation parameter equals `0`, lies strictly between `0` and
`1`, or is at least `1`, independently of selection and of the other
endpoint's parameter. For a general real parameter the analytic criteria
proved below are finiteness of `Σ` exactly below `1` and finiteness of `N`
exactly above `0`, so the exit pattern also occurs for negative parameters,
which are outside the population-genetics reading.

This is Feller's analytic integral test only: attainability or
non-attainability of the boundary, boundary conditions for a semigroup, and
existence or uniqueness of extensions are not claimed.

## References

* Karlin, S. and Taylor, H. M. (1981). *A Second Course in Stochastic
  Processes*. Academic Press, Chapter 15.
* Ewens, W. J. (2004). *Mathematical Population Genetics 1: Theoretical
  Introduction*. Second edition. Springer, Chapter 4.
-/

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

private theorem wrightFisher_left_speed_pos (α θ₁ θ₂ x : ℝ)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < selectionMutationSpeedDensity α θ₁ θ₂ x := by
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2]
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
    mul_assoc, mul_comm, mul_left_comm]
  positivity

private theorem wrightFisher_left_scale_pos (α θ₁ θ₂ x : ℝ)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < selectionMutationScaleDensity α θ₁ θ₂ x := by
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2]
  simp only [selectionMutationScaleDensity, mutationScaleDensity,
    mul_assoc, mul_comm, mul_left_comm]
  positivity

private theorem wrightFisher_left_split (f : ℝ → ℝ) (c : ℝ)
    (hc0 : 0 < c) :
    IntegrableOn f (Ioo 0 c) volume ↔
      IntegrableOn f (Ioo 0 (c / 2)) volume ∧
        IntegrableOn f (Ico (c / 2) c) volume := by
  have hc2pos : 0 < c / 2 := by linarith
  have hc2lt : c / 2 < c := by linarith
  have heq : Ioo 0 c = Ioo 0 (c / 2) ∪ Ico (c / 2) c := by
    ext x
    simp only [mem_Ioo, mem_Ico, mem_union]
    constructor
    · intro hx
      by_cases h : x < c / 2
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨le_of_not_gt h, hx.2⟩
    · intro hx
      rcases hx with ⟨hx0, hxc2⟩ | ⟨hxc2, hxc⟩
      · exact ⟨hx0, lt_trans hxc2 hc2lt⟩
      · exact ⟨lt_of_lt_of_le hc2pos hxc2, hxc⟩
  constructor
  · intro h
    have hsub1 : Ioo 0 (c / 2) ⊆ Ioo 0 c := by
      intro x hx
      exact ⟨hx.1, lt_trans hx.2 hc2lt⟩
    have hsub2 : Ico (c / 2) c ⊆ Ioo 0 c := by
      intro x hx
      exact ⟨lt_of_lt_of_le hc2pos hx.1, hx.2⟩
    exact ⟨h.mono_set hsub1, h.mono_set hsub2⟩
  · intro h
    rw [heq]
    exact h.1.union h.2

private theorem wrightFisher_left_continuous_speedFactor_on
    (α θ₂ : ℝ) {s : Set ℝ} (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (fun y : ℝ => Real.exp (2 * α * y) * (2 * (1 - y) ^ (θ₂ - 1)))
      s := by
  have hsub : ContinuousOn (fun y : ℝ => (1 : ℝ) - y) s :=
    continuousOn_const.sub continuousOn_id
  have hpow : ContinuousOn (fun y : ℝ => ((1 : ℝ) - y) ^ (θ₂ - 1)) s :=
    ContinuousOn.rpow_const hsub
      (fun y hy => Or.inl (ne_of_gt (by linarith [h1 y hy])))
  have hexp : ContinuousOn (fun y : ℝ => Real.exp (2 * α * y)) s :=
    Real.continuous_exp.comp_continuousOn'
      (continuousOn_const.mul continuousOn_id)
  exact hexp.mul (continuousOn_const.mul hpow)

private theorem wrightFisher_left_continuous_scaleFactor_on
    (α θ₂ : ℝ) {s : Set ℝ} (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (fun x : ℝ => Real.exp (-2 * α * x) * (1 - x) ^ (-θ₂))
      s := by
  have hsub : ContinuousOn (fun x : ℝ => (1 : ℝ) - x) s :=
    continuousOn_const.sub continuousOn_id
  have hpow : ContinuousOn (fun x : ℝ => ((1 : ℝ) - x) ^ (-θ₂)) s :=
    ContinuousOn.rpow_const hsub
      (fun x hx => Or.inl (ne_of_gt (by linarith [h1 x hx])))
  have hexp : ContinuousOn (fun x : ℝ => Real.exp (-2 * α * x)) s :=
    Real.continuous_exp.comp_continuousOn'
      (continuousOn_const.mul continuousOn_id)
  exact hexp.mul hpow

private theorem wrightFisher_left_speed_factor_eq (α θ₁ θ₂ y : ℝ) :
    selectionMutationSpeedDensity α θ₁ θ₂ y =
      Real.exp (2 * α * y) * (2 * (1 - y) ^ (θ₂ - 1)) * y ^ (θ₁ - 1) := by
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
    mul_assoc, mul_comm, mul_left_comm]

private theorem wrightFisher_left_scale_factor_eq (α θ₁ θ₂ x : ℝ) :
    selectionMutationScaleDensity α θ₁ θ₂ x =
      Real.exp (-2 * α * x) * (1 - x) ^ (-θ₂) * x ^ (-θ₁) := by
  simp only [selectionMutationScaleDensity, mutationScaleDensity,
    mul_assoc, mul_comm, mul_left_comm]

private theorem wrightFisher_left_continuous_speed_on
    (α θ₁ θ₂ : ℝ) {s : Set ℝ} (h0 : ∀ x ∈ s, 0 < x) (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (selectionMutationSpeedDensity α θ₁ θ₂) s := by
  have hF : ContinuousOn _ s :=
    wrightFisher_left_continuous_speedFactor_on α θ₂ h1
  have hpow : ContinuousOn (fun x : ℝ => x ^ (θ₁ - 1)) s :=
    ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt (h0 x hx)))
  exact (hF.mul hpow).congr
    (fun y hy => wrightFisher_left_speed_factor_eq α θ₁ θ₂ y)

private theorem wrightFisher_left_continuous_scale_on
    (α θ₁ θ₂ : ℝ) {s : Set ℝ} (h0 : ∀ x ∈ s, 0 < x) (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (selectionMutationScaleDensity α θ₁ θ₂) s := by
  have hF : ContinuousOn _ s :=
    wrightFisher_left_continuous_scaleFactor_on α θ₂ h1
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-θ₁)) s :=
    ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt (h0 x hx)))
  exact (hF.mul hpow).congr
    (fun y hy => wrightFisher_left_scale_factor_eq α θ₁ θ₂ y)

private theorem wrightFisher_left_factor_bound (f : ℝ → ℝ) (c : ℝ)
    (hc0 : 0 < c) (hcont : ContinuousOn f (Icc 0 c))
    (hpos : ∀ x ∈ Icc 0 c, 0 < f x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ y ∈ Ioo (0 : ℝ) c, m ≤ f y ∧ f y ≤ M := by
  have hcompact : IsCompact (Icc (0 : ℝ) c) := isCompact_Icc
  have hne : (Icc (0 : ℝ) c).Nonempty := ⟨0, mem_Icc.mpr ⟨le_rfl, le_of_lt hc0⟩⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨x0, hx0mem, hx0min⟩ := IsCompact.exists_isMinOn hcompact hne hcont
  have hmpos : 0 < f x0 := hpos x0 hx0mem
  refine ⟨f x0, M, hmpos, fun y hy => ?_⟩
  have hyIcc : y ∈ Icc (0 : ℝ) c := mem_Icc.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hleL : f x0 ≤ f y := (isMinOn_iff.mp hx0min) y hyIcc
  have hleU : f y ≤ M := by
    have hnorm : ‖f y‖ ≤ M := hM y hyIcc
    have hle : f y ≤ ‖f y‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact le_trans hle hnorm
  exact ⟨hleL, hleU⟩

private theorem wrightFisher_left_speed_bound (α θ₁ θ₂ c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ m M : ℝ, 0 < m ∧ ∀ y ∈ Ioo (0 : ℝ) c,
      m * y ^ (θ₁ - 1) ≤ selectionMutationSpeedDensity α θ₁ θ₂ y ∧
        selectionMutationSpeedDensity α θ₁ θ₂ y ≤ M * y ^ (θ₁ - 1) := by
  obtain ⟨hc0, hc1⟩ := hc
  have hcont : ContinuousOn _ (Icc 0 c) :=
    wrightFisher_left_continuous_speedFactor_on α θ₂
      (fun y hy => lt_of_le_of_lt hy.2 hc1)
  have hpos : ∀ y ∈ Icc (0 : ℝ) c,
      0 < Real.exp (2 * α * y) * (2 * (1 - y) ^ (θ₂ - 1)) := by
    intro y hy
    have h1y : (0 : ℝ) < 1 - y := by linarith [hy.2, hc1]
    positivity
  obtain ⟨m, M, hmpos, hbd⟩ :=
    wrightFisher_left_factor_bound _ c hc0 hcont hpos
  refine ⟨m, M, hmpos, fun y hy => ?_⟩
  have hrpow_nn : 0 ≤ y ^ (θ₁ - 1) := Real.rpow_nonneg (le_of_lt hy.1) _
  have heq := wrightFisher_left_speed_factor_eq α θ₁ θ₂ y
  obtain ⟨hlo, hhi⟩ := hbd y hy
  constructor
  · rw [heq]; exact mul_le_mul_of_nonneg_right hlo hrpow_nn
  · rw [heq]; exact mul_le_mul_of_nonneg_right hhi hrpow_nn

private theorem wrightFisher_left_scale_bound (α θ₁ θ₂ c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ Ioo (0 : ℝ) c,
      m * x ^ (-θ₁) ≤ selectionMutationScaleDensity α θ₁ θ₂ x ∧
        selectionMutationScaleDensity α θ₁ θ₂ x ≤ M * x ^ (-θ₁) := by
  obtain ⟨hc0, hc1⟩ := hc
  have hcont : ContinuousOn _ (Icc 0 c) :=
    wrightFisher_left_continuous_scaleFactor_on α θ₂
      (fun x hx => lt_of_le_of_lt hx.2 hc1)
  have hpos : ∀ x ∈ Icc (0 : ℝ) c,
      0 < Real.exp (-2 * α * x) * (1 - x) ^ (-θ₂) := by
    intro x hx
    have h1x : (0 : ℝ) < 1 - x := by linarith [hx.2, hc1]
    positivity
  obtain ⟨m, M, hmpos, hbd⟩ :=
    wrightFisher_left_factor_bound _ c hc0 hcont hpos
  refine ⟨m, M, hmpos, fun x hx => ?_⟩
  have hrpow_nn : 0 ≤ x ^ (-θ₁) := Real.rpow_nonneg (le_of_lt hx.1) _
  have heq := wrightFisher_left_scale_factor_eq α θ₁ θ₂ x
  obtain ⟨hlo, hhi⟩ := hbd x hx
  constructor
  · rw [heq]; exact mul_le_mul_of_nonneg_right hlo hrpow_nn
  · rw [heq]; exact mul_le_mul_of_nonneg_right hhi hrpow_nn

private theorem wrightFisher_left_inner_ge (Inner : ℝ → ℝ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hInner_nn : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ Inner y)
    (hInner_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < Inner y)
    (hInner_cont : ∀ d : ℝ, 0 < d → d < c → ContinuousOn Inner (Icc d c)) :
    (∀ x ∈ Ioo (0 : ℝ) (c / 2), (∫ y in (c / 2)..c, Inner y) ≤
      (∫ y in x..c, Inner y) ∧ 0 ≤ ∫ y in x..c, Inner y) ∧
      0 < ∫ y in (c / 2)..c, Inner y := by
  have hc2pos : 0 < c / 2 := by linarith
  have hc2lt : c / 2 < c := by linarith
  have hcont_c2 : ContinuousOn Inner (Icc (c / 2) c) :=
    hInner_cont (c / 2) hc2pos hc2lt
  have hInt_c2 : IntervalIntegrable _ volume (c / 2) c :=
    hcont_c2.intervalIntegrable_of_Icc hc2lt.le
  have hP : 0 < ∫ y in (c / 2)..c, Inner y :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hInt_c2
      (fun x hx => hInner_pos x ⟨lt_trans hc2pos hx.1, lt_trans hx.2 hc1⟩) hc2lt
  refine ⟨fun x hx => ?_, hP⟩
  have hx0 : 0 < x := hx.1
  have hxc : x < c := lt_trans hx.2 hc2lt
  have hInt_xc : IntervalIntegrable _ volume x c :=
    (hInner_cont x hx0 hxc).intervalIntegrable_of_Icc hxc.le
  have hf : 0 ≤ᵐ[volume.restrict (Ioc x c)] Inner := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
    exact hInner_nn y ⟨lt_trans hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩
  have hge : (∫ y in (c / 2)..c, Inner y) ≤ ∫ y in x..c, Inner y :=
    intervalIntegral.integral_mono_interval (le_of_lt hx.2) hc2lt.le le_rfl hf
      hInt_xc
  have hnn : 0 ≤ ∫ y in x..c, Inner y :=
    intervalIntegral.integral_nonneg hxc.le
      (fun y hy => hInner_nn y ⟨lt_of_lt_of_le hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩)
  exact ⟨hge, hnn⟩

private theorem wrightFisher_left_cancel (α θ₁ θ₂ c : ℝ) (hc0 : 0 < c)
    (hc1 : c < 1) :
    (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) = 1 := by
  have h1cpos : 0 < 1 - c := by linarith
  have hr1 : c ^ (-θ₁) * c ^ θ₁ = 1 := by
    rw [← Real.rpow_add hc0, show (-θ₁ : ℝ) + θ₁ = 0 by ring, Real.rpow_zero]
  have hr2 : (1 - c) ^ (-θ₂) * (1 - c) ^ θ₂ = 1 := by
    rw [← Real.rpow_add h1cpos, show (-θ₂ : ℝ) + θ₂ = 0 by ring, Real.rpow_zero]
  have he : Real.exp (-2 * α * c) * Real.exp (2 * α * c) = 1 := by
    rw [← Real.exp_add, show -2 * α * c + 2 * α * c = 0 by ring, Real.exp_zero]
  have hring : (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
          (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) =
        (c ^ (-θ₁) * c ^ θ₁) * ((1 - c) ^ (-θ₂) * (1 - c) ^ θ₂) *
          (Real.exp (-2 * α * c) * Real.exp (2 * α * c)) := by
    ring
  rw [hring, hr1, hr2, he, mul_one, mul_one]

private theorem wrightFisher_left_Feller_mp
    {Inner Outer : ℝ → ℝ} {P m r : ℝ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hP : 0 < P) (hm : 0 < m) (hr : r ≤ -1)
    (hInner : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      P ≤ (∫ y in x..c, Inner y) ∧ 0 ≤ ∫ y in x..c, Inner y)
    (hOuter : ∀ x ∈ Ioo (0 : ℝ) (c / 2), m * x ^ r ≤ Outer x ∧ 0 ≤ Outer x)
    (hInt : IntegrableOn (fun x => (∫ y in x..c, Inner y) * Outer x)
      (Ioo (0 : ℝ) (c / 2)) volume) :
    False := by
  have hrpow_nint : ¬ IntegrableOn (fun x => x ^ r) (Ioo 0 (c / 2)) volume :=
    mt (intervalIntegral.integrableOn_Ioo_rpow_iff (by linarith)).mp
      (not_lt.mpr hr)
  have hcont_pow : ContinuousOn (fun x : ℝ => x ^ r) (Ioo 0 (c / 2)) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt hx.1))
  have hKpos : 0 < P * m := mul_pos hP hm
  have hle : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))),
      ((P * m) * x ^ r) ≤ (∫ y in x..c, Inner y) * Outer x := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have heq0 : (P * m) * x ^ r = P * (m * x ^ r) := by ring
    calc (P * m) * x ^ r = P * (m * x ^ r) := heq0
      _ ≤ P * Outer x :=
        mul_le_mul_of_nonneg_left (hOuter x hx).1 (le_of_lt hP)
      _ ≤ (∫ y in x..c, Inner y) * Outer x :=
        mul_le_mul_of_nonneg_right (hInner x hx).1 (hOuter x hx).2
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))), 0 ≤ x ^ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg (le_of_lt hx.1) _
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ r)
      (volume.restrict (Ioo 0 (c / 2))) :=
    hcont_pow.aestronglyMeasurable measurableSet_Ioo
  have hKne : P * m ≠ 0 := ne_of_gt hKpos
  have hKinv_nn : 0 ≤ (P * m)⁻¹ := inv_nonneg.mpr (le_of_lt hKpos)
  have hFavsmul : Integrable _ (volume.restrict (Ioo 0 (c / 2))) :=
    hInt.const_mul (P * m)⁻¹
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))),
      ‖x ^ r‖ ≤ (P * m)⁻¹ * ((∫ y in x..c, Inner y) * Outer x) := by
    filter_upwards [hle, hnn] with x hx hnx
    rw [Real.norm_eq_abs, abs_of_nonneg hnx]
    have h2 : (P * m)⁻¹ * ((P * m) * x ^ r) = x ^ r := by
      rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
    calc x ^ r = (P * m)⁻¹ * ((P * m) * x ^ r) := h2.symm
      _ ≤ (P * m)⁻¹ * ((∫ y in x..c, Inner y) * Outer x) :=
        mul_le_mul_of_nonneg_left hx hKinv_nn
  have hint : IntegrableOn _ (Ioo 0 (c / 2)) volume :=
    hFavsmul.mono' hmeas hbound
  exact hrpow_nint hint

private theorem wrightFisher_left_regular (I O : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c)
    (hI : ContinuousOn I (Icc (c / 2) c)) (hO : ContinuousOn O (Icc (c / 2) c)) :
    IntegrableOn (fun x => (∫ y in x..c, I y) * O x) (Ico (c / 2) c) volume := by
  have hc2le : c / 2 ≤ c := by linarith
  have hI' : IntegrableOn I (uIcc (c / 2) c) volume := by
    rw [uIcc_of_le hc2le]; exact hI.integrableOn_Icc
  have hP : ContinuousOn (fun x => ∫ y in x..c, I y) (Icc (c / 2) c) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left hI'
    rwa [uIcc_of_le hc2le] at h
  exact (hP.mul hO).integrableOn_Icc.mono_set Ico_subset_Icc_self

private theorem wrightFisher_left_singular_sufficiency
    (Inner Outer : ℝ → ℝ) (c p q M₁ M₂ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hpq : p + q + 1 = 0) (hpneg : p < 0)
    (hInner_bound : ∀ y ∈ Ioo (0 : ℝ) c, Inner y ≤ M₁ * y ^ p)
    (hOuter_bound : ∀ x ∈ Ioo (0 : ℝ) (c / 2), Outer x ≤ M₂ * x ^ q)
    (hInner_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < Inner y)
    (hOuter_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < Outer x)
    (hInner_cont : ∀ d : ℝ, 0 < d → d < c → ContinuousOn Inner (Icc d c))
    (hOuter_cont : ContinuousOn Outer (Ioo (0 : ℝ) (c / 2))) :
    IntegrableOn (fun x => (∫ y in x..c, Inner y) * Outer x)
      (Ioo (0 : ℝ) (c / 2)) volume := by
  have hc2pos : 0 < c / 2 := by linarith
  have hc2lt : c / 2 < c := by linarith
  have hM₁ : 0 < M₁ := by
    have hI := hInner_bound (c / 2) ⟨hc2pos, hc2lt⟩
    have hP := hInner_pos (c / 2) ⟨hc2pos, by linarith⟩
    have hrp : 0 < (c / 2) ^ p := Real.rpow_pos_of_pos hc2pos p
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonpos_of_nonneg hcon hrp.le
    linarith
  have hM₂ : 0 < M₂ := by
    have hO := hOuter_bound (c / 4) ⟨by linarith, by linarith⟩
    have hP := hOuter_pos (c / 4) ⟨by linarith, by linarith⟩
    have hrp : 0 < (c / 4) ^ q := Real.rpow_pos_of_pos (by linarith) q
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonpos_of_nonneg hcon hrp.le
    linarith
  have hC₂_nn : 0 ≤ ∫ y in (c / 2)..c, Inner y :=
    intervalIntegral.integral_nonneg hc2lt.le (fun y hy =>
      le_of_lt (hInner_pos y ⟨lt_of_lt_of_le hc2pos hy.1,
        lt_of_le_of_lt hy.2 hc1⟩))
  have hsplit : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      (∫ y in x..c, Inner y) =
        (∫ y in x..(c / 2), Inner y) + ∫ y in (c / 2)..c, Inner y := by
    intro x hx
    have hxc : x < c := lt_trans hx.2 hc2lt
    have hcont : ContinuousOn Inner (Icc x c) := hInner_cont x hx.1 hxc
    have hxc2 : IntervalIntegrable Inner volume x (c / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (hcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hc2lt.le⟩))
    have hc2c : IntervalIntegrable Inner volume (c / 2) c :=
      ContinuousOn.intervalIntegrable_of_Icc hc2lt.le
        (hcont.mono (fun y hy => ⟨le_trans hx.2.le hy.1, hy.2⟩))
    exact (intervalIntegral.integral_add_adjacent_intervals hxc2 hc2c).symm
  have hJ : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      (∫ y in x..(c / 2), Inner y) ≤ M₁ * ∫ y in x..(c / 2), y ^ p := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := lt_trans hx.2 hc2lt
    have hcont : ContinuousOn Inner (Icc x c) := hInner_cont x hx0 hxc
    have hIx : IntervalIntegrable Inner volume x (c / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (hcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hc2lt.le⟩))
    have hpow : ContinuousOn (fun y : ℝ => y ^ p) (Icc x (c / 2)) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun y hy => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hy.1)))
    have hIp : IntervalIntegrable (fun y : ℝ => M₁ * y ^ p) volume x (c / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (continuousOn_const.mul hpow)
    have hmono := intervalIntegral.integral_mono_on hx.2.le hIx hIp
      (fun y hy => hInner_bound y ⟨lt_of_lt_of_le hx0 hy.1,
        lt_of_le_of_lt hy.2 hc2lt⟩)
    rwa [intervalIntegral.integral_const_mul M₁ (fun y : ℝ => y ^ p)] at hmono
  have hFcont : ContinuousOn (fun x => (∫ y in x..c, Inner y) * Outer x)
      (Ioo (0 : ℝ) (c / 2)) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := lt_trans hx.2 hc2lt
    have hd0 : 0 < x / 2 := by linarith
    have hdx : x / 2 < x := by linarith
    have hdc : x / 2 < c := lt_trans hdx hxc
    have hIc : ContinuousOn Inner (Icc (x / 2) c) :=
      hInner_cont (x / 2) hd0 hdc
    have hIu : IntegrableOn Inner (uIcc (x / 2) c) volume := by
      rw [uIcc_of_le hdc.le]; exact hIc.integrableOn_Icc
    have hP : ContinuousOn (fun x => ∫ y in x..c, Inner y) (Icc (x / 2) c) := by
      have h := intervalIntegral.continuousOn_primitive_interval_left hIu
      rwa [uIcc_of_le hdc.le] at h
    have hmem : Icc (x / 2) c ∈ 𝓝 x :=
      Filter.mem_of_superset (Ioo_mem_nhds hdx hxc) Ioo_subset_Icc_self
    have hprim : ContinuousAt (fun x => ∫ y in x..c, Inner y) x :=
      hP.continuousAt hmem
    have hout : ContinuousAt Outer x :=
      hOuter_cont.continuousAt (IsOpen.mem_nhds isOpen_Ioo hx)
    exact (hprim.mul hout).continuousWithinAt
  have hInner_nn : ∀ x ∈ Ioo (0 : ℝ) (c / 2), 0 ≤ ∫ y in x..c, Inner y := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := lt_trans hx.2 hc2lt
    exact intervalIntegral.integral_nonneg hxc.le (fun y hy =>
      le_of_lt (hInner_pos y ⟨lt_of_lt_of_le hx0 hy.1,
        lt_of_le_of_lt hy.2 hc1⟩))
  have hOuter_nn : ∀ x ∈ Ioo (0 : ℝ) (c / 2), 0 ≤ Outer x :=
    fun x hx => le_of_lt
      (hOuter_pos x ⟨hx.1, lt_trans (lt_trans hx.2 hc2lt) hc1⟩)
  have hFnn : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      0 ≤ (∫ y in x..c, Inner y) * Outer x :=
    fun x hx => mul_nonneg (hInner_nn x hx) (hOuter_nn x hx)
  have hprod : ∀ a b U V : ℝ, a ≤ U → b ≤ V → 0 ≤ b → 0 ≤ U → a * b ≤ U * V :=
    fun a b U V h1 h2 hb hU => le_trans (mul_le_mul_of_nonneg_right h1 hb)
      (mul_le_mul_of_nonneg_left h2 hU)
  have hFmeas : AEStronglyMeasurable
      (fun x => (∫ y in x..c, Inner y) * Outer x)
      (volume.restrict (Ioo (0 : ℝ) (c / 2))) :=
    hFcont.aestronglyMeasurable measurableSet_Ioo
  have hq_int : IntegrableOn (fun x : ℝ => x ^ q) (Ioo 0 (c / 2)) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hc2pos).mpr (by linarith)
  have hfin : volume (Ioo (0 : ℝ) (c / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ne_of_lt ENNReal.ofReal_lt_top
  rcases lt_trichotomy p (-1) with hlt | heq | hgt
  · have hDpos : 0 < -(p + 1) := by linarith
    have hne : p ≠ -1 := ne_of_lt hlt
    have hne1 : p + 1 ≠ 0 := ne_of_lt (by linarith)
    have hne2 : -(p + 1) ≠ 0 := ne_of_gt hDpos
    have hpow_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..(c / 2), y ^ p) ≤ x ^ (p + 1) / (-(p + 1)) := by
      intro x hx
      have h0mem : (0 : ℝ) ∉ uIcc x (c / 2) := by
        rw [uIcc_of_le hx.2.le]
        intro hcon
        have hx0' : x ≤ 0 := (mem_Icc.mp hcon).1
        linarith [hx.1]
      rw [integral_rpow (Or.inr ⟨hne, h0mem⟩)]
      have hflip : ((c / 2) ^ (p + 1) - x ^ (p + 1)) / (p + 1) =
          (x ^ (p + 1) - (c / 2) ^ (p + 1)) / (-(p + 1)) := by
        field_simp
        ring
      rw [hflip]
      have hnum : x ^ (p + 1) - (c / 2) ^ (p + 1) ≤ x ^ (p + 1) := by
        have hnn : 0 ≤ (c / 2) ^ (p + 1) := Real.rpow_nonneg hc2pos.le _
        linarith
      exact div_le_div_of_nonneg_right hnum hDpos.le
    have hInner_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..c, Inner y) ≤ M₁ * (x ^ (p + 1) / (-(p + 1))) +
          ∫ y in (c / 2)..c, Inner y := by
      intro x hx
      rw [hsplit x hx]
      have h1 := mul_le_mul_of_nonneg_left (hpow_le x hx) hM₁.le
      linarith [hJ x hx]
    have hpt : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ M₁ * M₂ / (-(p + 1)) +
          (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hrw : x ^ (p + 1) * x ^ q = 1 := by
        rw [← Real.rpow_add hx0, show (p + 1) + q = 0 by linarith,
          Real.rpow_zero]
      have hU_nn : 0 ≤ M₁ * (x ^ (p + 1) / (-(p + 1))) +
          (∫ y in (c / 2)..c, Inner y) :=
        add_nonneg (mul_nonneg hM₁.le
          (div_pos (Real.rpow_pos_of_pos hx0 _) hDpos).le) hC₂_nn
      have hmul : (∫ y in x..c, Inner y) * Outer x ≤
          (M₁ * (x ^ (p + 1) / (-(p + 1))) +
            (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) :=
        hprod _ _ _ _ (hInner_le x hx) (hOuter_bound x hx) (hOuter_nn x hx) hU_nn
      have e1 : M₁ * (x ^ (p + 1) / (-(p + 1))) * (M₂ * x ^ q) =
          M₁ * M₂ / (-(p + 1)) * (x ^ (p + 1) * x ^ q) := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x hx)]
      calc (∫ y in x..c, Inner y) * Outer x
          ≤ (M₁ * (x ^ (p + 1) / (-(p + 1))) +
              (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) := hmul
        _ = M₁ * M₂ / (-(p + 1)) +
            (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q := by
            rw [add_mul, e1, hrw, mul_one]
            ring
    have hg : IntegrableOn (fun x => M₁ * M₂ / (-(p + 1)) +
        (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q)
        (Ioo (0 : ℝ) (c / 2)) volume := by
      have h1 : IntegrableOn (fun _ => M₁ * M₂ / (-(p + 1)))
          (Ioo (0 : ℝ) (c / 2)) volume := integrableOn_const hfin
      have h2 : IntegrableOn
          (fun x => (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q)
          (Ioo (0 : ℝ) (c / 2)) volume :=
        hq_int.const_mul ((∫ y in (c / 2)..c, Inner y) * M₂)
      exact h1.add h2
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (c / 2))),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ M₁ * M₂ / (-(p + 1)) +
          (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    exact hg.mono' hFmeas hbound
  · have hq0 : q = 0 := by linarith
    have hs_int : IntegrableOn (fun x : ℝ => x ^ (-1 / 2 : ℝ))
        (Ioo 0 (c / 2)) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hc2pos).mpr (by linarith)
    have hlog_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        -Real.log x ≤ 2 * x ^ (-1 / 2 : ℝ) := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hspos : 0 < x ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
      have hrpow : Real.log (x ^ (-1 / 2 : ℝ)) = (-1 / 2 : ℝ) * Real.log x :=
        Real.log_rpow hx0 _
      have hle : Real.log (x ^ (-1 / 2 : ℝ)) ≤ x ^ (-1 / 2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hspos
      have hlogeq : -Real.log x = 2 * Real.log (x ^ (-1 / 2 : ℝ)) := by
        rw [hrpow]; ring
      rw [hlogeq]
      linarith
    have hInner_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..c, Inner y) ≤ M₁ * (Real.log (c / 2) - Real.log x) +
          (∫ y in (c / 2)..c, Inner y) := by
      intro x hx
      rw [hsplit x hx]
      have h1 := hJ x hx
      have hftc : (∫ y in x..(c / 2), y ^ p) =
          Real.log (c / 2) - Real.log x := by
        rw [heq]
        simp only [Real.rpow_neg_one]
        rw [integral_inv_of_pos hx.1 hc2pos,
          Real.log_div (ne_of_gt hc2pos) (ne_of_gt hx.1)]
      rw [hftc] at h1
      linarith
    have hOuter_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2), Outer x ≤ M₂ := by
      intro x hx
      have h := hOuter_bound x hx
      rw [hq0, Real.rpow_zero, mul_one] at h
      exact h
    have hL : Real.log (c / 2) ≤ 0 :=
      le_of_lt (Real.log_neg hc2pos (by linarith))
    have hpt : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) +
          (∫ y in (c / 2)..c, Inner y) * M₂ := by
      intro x hx
      have hlog := hlog_le x hx
      have hU_nn : 0 ≤ M₁ * (Real.log (c / 2) - Real.log x) +
          (∫ y in (c / 2)..c, Inner y) :=
        add_nonneg (mul_nonneg hM₁.le
          (sub_pos.mpr (Real.log_lt_log hx.1 hx.2)).le) hC₂_nn
      have hmul : (∫ y in x..c, Inner y) * Outer x ≤
          (M₁ * (Real.log (c / 2) - Real.log x) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ :=
        hprod _ _ _ _ (hInner_le x hx) (hOuter_le x hx) (hOuter_nn x hx) hU_nn
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x hx)]
      have hexpand : (M₁ * (Real.log (c / 2) - Real.log x) +
          (∫ y in (c / 2)..c, Inner y)) * M₂ =
          M₁ * M₂ * (Real.log (c / 2) - Real.log x) +
            (∫ y in (c / 2)..c, Inner y) * M₂ := by ring
      rw [hexpand] at hmul
      have hLe : M₁ * M₂ * (Real.log (c / 2) - Real.log x) ≤
          2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) := by
        have hMM : 0 ≤ M₁ * M₂ := mul_nonneg hM₁.le hM₂.le
        have hsum : Real.log (c / 2) - Real.log x ≤
            2 * x ^ (-1 / 2 : ℝ) := by
          linarith
        calc M₁ * M₂ * (Real.log (c / 2) - Real.log x)
            = (M₁ * M₂) * (Real.log (c / 2) - Real.log x) := by ring
          _ ≤ (M₁ * M₂) * (2 * x ^ (-1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hsum hMM
          _ = 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) := by ring
      linarith [hmul, hLe]
    have hg : IntegrableOn (fun x => 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) +
        (∫ y in (c / 2)..c, Inner y) * M₂)
        (Ioo (0 : ℝ) (c / 2)) volume := by
      have h1 : IntegrableOn (fun _ => (∫ y in (c / 2)..c, Inner y) * M₂)
          (Ioo (0 : ℝ) (c / 2)) volume := integrableOn_const hfin
      have h2 : IntegrableOn (fun x => 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ))
          (Ioo (0 : ℝ) (c / 2)) volume :=
        hs_int.const_mul (2 * M₁ * M₂)
      exact h2.add h1
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (c / 2))),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) +
          (∫ y in (c / 2)..c, Inner y) * M₂ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    exact hg.mono' hFmeas hbound
  · have hPpos : 0 < p + 1 := by linarith
    have hpow_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..(c / 2), y ^ p) ≤ (c / 2) ^ (p + 1) / (p + 1) := by
      intro x hx
      rw [integral_rpow (Or.inl hgt)]
      have hnum : (c / 2) ^ (p + 1) - x ^ (p + 1) ≤ (c / 2) ^ (p + 1) := by
        have hnn : 0 ≤ x ^ (p + 1) := Real.rpow_nonneg hx.1.le _
        linarith
      exact div_le_div_of_nonneg_right hnum hPpos.le
    have hK1 : 0 < M₁ * ((c / 2) ^ (p + 1) / (p + 1)) :=
      mul_pos hM₁ (div_pos (Real.rpow_pos_of_pos hc2pos _) hPpos)
    have hInner_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..c, Inner y) ≤ M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
          (∫ y in (c / 2)..c, Inner y) := by
      intro x hx
      rw [hsplit x hx]
      have h1 := mul_le_mul_of_nonneg_left (hpow_le x hx) hM₁.le
      linarith [hJ x hx]
    have hK_nn : 0 ≤ M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
        (∫ y in (c / 2)..c, Inner y) := add_nonneg hK1.le hC₂_nn
    have hpt : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q := by
      intro x hx
      have hmul : (∫ y in x..c, Inner y) * Outer x ≤
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) :=
        hprod _ _ _ _ (hInner_le x hx) (hOuter_bound x hx) (hOuter_nn x hx) hK_nn
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x hx)]
      have heq : (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
          (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) =
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q := by ring
      rwa [heq] at hmul
    have hg : IntegrableOn (fun x => (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
        (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q)
        (Ioo (0 : ℝ) (c / 2)) volume :=
      hq_int.const_mul ((M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
        (∫ y in (c / 2)..c, Inner y)) * M₂)
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (c / 2))),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    exact hg.mono' hFmeas hbound

private theorem integrableOn_wrightFisher_left_sigma_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔ θ₁ < 1 := by
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  have hc2lt : c / 2 < c := by linarith
  let G : ℝ → ℝ := fun x =>
    (∫ y in x..c, selectionMutationSpeedDensity α θ₁ θ₂ y) *
      selectionMutationScaleDensity α θ₁ θ₂ x
  have hEq : Set.EqOn (fun x => (∫ y in x..c, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) G (Ioo 0 c) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, lt_trans hxc hc1⟩
    have hinner : (∫ y in x..c, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) =
        (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
          (∫ y in x..c, selectionMutationSpeedDensity α θ₁ θ₂ y) := by
      have hpoint : ∀ y ∈ Ioc x c, speedDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y =
          (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
            selectionMutationSpeedDensity α θ₁ θ₂ y :=
        fun y hy => speedDensityFrom_selectionMutation α θ₁ θ₂ c y hc
          ⟨lt_trans hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩
      have hIoc : uIoc x c = Ioc x c := uIoc_of_le (le_of_lt hxc)
      have hcongr : (∫ y in x..c, speedDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y) =
          (∫ y in x..c, (c ^ (-θ₁) * (1 - c) ^ (-θ₂) *
            Real.exp (-2 * α * c)) *
            selectionMutationSpeedDensity α θ₁ θ₂ y) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [hIoc]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
        exact hpoint y hy
      rw [hcongr, intervalIntegral.integral_const_mul]
    have houter : scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
          selectionMutationScaleDensity α θ₁ θ₂ x :=
      scaleDensityFrom_selectionMutation α θ₁ θ₂ c x hc hx01
    have hcancel := wrightFisher_left_cancel α θ₁ θ₂ c hc0 hc1
    have hgoal : (∫ y in x..c, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (∫ y in x..c, selectionMutationSpeedDensity α θ₁ θ₂ y) *
          selectionMutationScaleDensity α θ₁ θ₂ x := by
      rw [hinner, houter, mul_mul_mul_comm, hcancel, one_mul]
    exact hgoal
  have hFiff : IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔
      IntegrableOn G (Ioo 0 c) volume :=
    ⟨fun h => h.congr_fun hEq measurableSet_Ioo,
      fun h => h.congr_fun (fun x hx => (hEq hx).symm) measurableSet_Ioo⟩
  rw [hFiff]
  have hsplit := wrightFisher_left_split G c hc0
  have hspeed_fun : ∀ d : ℝ, 0 < d → d < c →
      ContinuousOn (selectionMutationSpeedDensity α θ₁ θ₂) (Icc d c) :=
    fun d hd0 _hdc => wrightFisher_left_continuous_speed_on α θ₁ θ₂
      (fun y hy => lt_of_lt_of_le hd0 hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
  obtain ⟨m₂, _, hm₂, hscale⟩ := wrightFisher_left_scale_bound α θ₁ θ₂ c hc
  have hspeed_nn : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ selectionMutationSpeedDensity α θ₁ θ₂ y :=
    fun y hy => le_of_lt (wrightFisher_left_speed_pos α θ₁ θ₂ y hy)
  have hspeed_pos' : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < selectionMutationSpeedDensity α θ₁ θ₂ y :=
    fun y hy => wrightFisher_left_speed_pos α θ₁ θ₂ y hy
  have hInner_full := wrightFisher_left_inner_ge _ _ hc0 hc1 hspeed_nn hspeed_pos' hspeed_fun
  have hsing : IntegrableOn G (Ioo 0 (c / 2)) volume ↔ θ₁ < 1 := by
    constructor
    · intro hInt
      by_contra hcon
      have hle : 1 ≤ θ₁ := le_of_not_gt hcon
      have hr : -θ₁ ≤ -1 := by linarith
      have hOuter : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
          m₂ * x ^ (-θ₁) ≤ selectionMutationScaleDensity α θ₁ θ₂ x ∧
            0 ≤ selectionMutationScaleDensity α θ₁ θ₂ x := by
        intro x hx
        exact ⟨(hscale x ⟨hx.1, lt_trans hx.2 hc2lt⟩).1,
          le_of_lt (wrightFisher_left_scale_pos α θ₁ θ₂ x
            ⟨hx.1, lt_trans (lt_trans hx.2 hc2lt) hc1⟩)⟩
      have hfalse : False :=
        wrightFisher_left_Feller_mp hc0 hc1 hInner_full.2 hm₂ hr hInner_full.1
          hOuter hInt
      exact hfalse.elim
    · intro h
      obtain ⟨_, M₁, _, hspeed⟩ := wrightFisher_left_speed_bound α θ₁ θ₂ c hc
      exact wrightFisher_left_singular_sufficiency _ _ c (θ₁ - 1) (-θ₁) _ _
        hc0 hc1 (by ring) (by linarith) (fun y hy => (hspeed y hy).2)
        (fun x hx => (hscale x ⟨hx.1, lt_trans hx.2 hc2lt⟩).2)
        (fun y hy => wrightFisher_left_speed_pos α θ₁ θ₂ y hy)
        (fun x hx => wrightFisher_left_scale_pos α θ₁ θ₂ x hx) hspeed_fun
        (wrightFisher_left_continuous_scale_on α θ₁ θ₂ (fun y hy => hy.1)
          (fun y hy => lt_trans (lt_trans hy.2 hc2lt) hc1))
  rw [hsplit]
  constructor
  · intro h
    exact hsing.mp h.1
  · intro h
    refine ⟨hsing.mpr h, ?_⟩
    have hc2pos : 0 < c / 2 := by linarith
    have hO : ContinuousOn (selectionMutationScaleDensity α θ₁ θ₂) (Icc (c/2) c) :=
      wrightFisher_left_continuous_scale_on α θ₁ θ₂
        (fun y hy => lt_of_lt_of_le hc2pos hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
    exact wrightFisher_left_regular _ _ c hc0 (hspeed_fun (c/2) hc2pos hc2lt) hO

private theorem integrableOn_wrightFisher_left_scale_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔ 0 < θ₁ := by
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  have hc2lt : c / 2 < c := by linarith
  let G : ℝ → ℝ := fun x =>
    (∫ y in x..c, selectionMutationScaleDensity α θ₁ θ₂ y) *
      selectionMutationSpeedDensity α θ₁ θ₂ x
  have hEq : Set.EqOn (fun x => (∫ y in x..c, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) G (Ioo 0 c) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, lt_trans hxc hc1⟩
    have hinner : (∫ y in x..c, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) =
        (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
          (∫ y in x..c, selectionMutationScaleDensity α θ₁ θ₂ y) := by
      have hpoint : ∀ y ∈ Ioc x c, scaleDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y =
          (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
            selectionMutationScaleDensity α θ₁ θ₂ y :=
        fun y hy => scaleDensityFrom_selectionMutation α θ₁ θ₂ c y hc
          ⟨lt_trans hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩
      have hIoc : uIoc x c = Ioc x c := uIoc_of_le (le_of_lt hxc)
      have hcongr : (∫ y in x..c, scaleDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y) =
          (∫ y in x..c, (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
            selectionMutationScaleDensity α θ₁ θ₂ y) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [hIoc]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
        exact hpoint y hy
      rw [hcongr, intervalIntegral.integral_const_mul]
    have houter : speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
          selectionMutationSpeedDensity α θ₁ θ₂ x :=
      speedDensityFrom_selectionMutation α θ₁ θ₂ c x hc hx01
    have hcancel := wrightFisher_left_cancel α θ₁ θ₂ c hc0 hc1
    have hgoal : (∫ y in x..c, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (∫ y in x..c, selectionMutationScaleDensity α θ₁ θ₂ y) *
          selectionMutationSpeedDensity α θ₁ θ₂ x := by
      rw [hinner, houter, mul_mul_mul_comm]
      have hcancel' : (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
          (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) = 1 := by
        rw [mul_comm]; exact hcancel
      rw [hcancel', one_mul]
    exact hgoal
  have hFiff : IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔
      IntegrableOn G (Ioo 0 c) volume :=
    ⟨fun h => h.congr_fun hEq measurableSet_Ioo,
      fun h => h.congr_fun (fun x hx => (hEq hx).symm) measurableSet_Ioo⟩
  rw [hFiff]
  have hsplit := wrightFisher_left_split G c hc0
  have hscale_fun : ∀ d : ℝ, 0 < d → d < c →
      ContinuousOn (selectionMutationScaleDensity α θ₁ θ₂) (Icc d c) :=
    fun d hd0 _hdc => wrightFisher_left_continuous_scale_on α θ₁ θ₂
      (fun y hy => lt_of_lt_of_le hd0 hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
  obtain ⟨m₁, _, hm₁, hspeed⟩ := wrightFisher_left_speed_bound α θ₁ θ₂ c hc
  have hscale_nn : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ selectionMutationScaleDensity α θ₁ θ₂ y :=
    fun y hy => le_of_lt (wrightFisher_left_scale_pos α θ₁ θ₂ y hy)
  have hscale_pos' : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < selectionMutationScaleDensity α θ₁ θ₂ y :=
    fun y hy => wrightFisher_left_scale_pos α θ₁ θ₂ y hy
  have hInner_full := wrightFisher_left_inner_ge _ _ hc0 hc1 hscale_nn hscale_pos' hscale_fun
  have hsing : IntegrableOn G (Ioo 0 (c / 2)) volume ↔ 0 < θ₁ := by
    constructor
    · intro hInt
      by_contra hcon
      have hle : θ₁ ≤ 0 := le_of_not_gt hcon
      have hr : θ₁ - 1 ≤ -1 := by linarith
      have hOuter : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
          m₁ * x ^ (θ₁ - 1) ≤ selectionMutationSpeedDensity α θ₁ θ₂ x ∧
            0 ≤ selectionMutationSpeedDensity α θ₁ θ₂ x := by
        intro x hx
        exact ⟨(hspeed x ⟨hx.1, lt_trans hx.2 hc2lt⟩).1,
          le_of_lt (wrightFisher_left_speed_pos α θ₁ θ₂ x
            ⟨hx.1, lt_trans (lt_trans hx.2 hc2lt) hc1⟩)⟩
      have hfalse : False :=
        wrightFisher_left_Feller_mp hc0 hc1 hInner_full.2 hm₁ hr hInner_full.1
          hOuter hInt
      exact hfalse.elim
    · intro h
      obtain ⟨_, M₂, _, hscale⟩ := wrightFisher_left_scale_bound α θ₁ θ₂ c hc
      exact wrightFisher_left_singular_sufficiency _ _ c (-θ₁) (θ₁ - 1) _ _
        hc0 hc1 (by ring) (by linarith) (fun y hy => (hscale y hy).2)
        (fun x hx => (hspeed x ⟨hx.1, lt_trans hx.2 hc2lt⟩).2)
        (fun y hy => wrightFisher_left_scale_pos α θ₁ θ₂ y hy)
        (fun x hx => wrightFisher_left_speed_pos α θ₁ θ₂ x hx) hscale_fun
        (wrightFisher_left_continuous_speed_on α θ₁ θ₂ (fun y hy => hy.1)
          (fun y hy => lt_trans (lt_trans hy.2 hc2lt) hc1))
  rw [hsplit]
  constructor
  · intro h
    exact hsing.mp h.1
  · intro h
    refine ⟨hsing.mpr h, ?_⟩
    have hc2pos : 0 < c / 2 := by linarith
    have hO : ContinuousOn (selectionMutationSpeedDensity α θ₁ θ₂) (Icc (c/2) c) :=
      wrightFisher_left_continuous_speed_on α θ₁ θ₂
        (fun y hy => lt_of_lt_of_le hc2pos hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
    exact wrightFisher_left_regular _ _ c hc0 (hscale_fun (c/2) hc2pos hc2lt) hO

private theorem wrightFisher_right_speed_reflect (α θ₁ θ₂ z : ℝ) :
    selectionMutationSpeedDensity α θ₁ θ₂ (1 - z) =
      Real.exp (2 * α) * selectionMutationSpeedDensity (-α) θ₂ θ₁ z := by
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity]
  have h1 : (1 : ℝ) - (1 - z) = z := by ring
  have hexp : 2 * α * (1 - z) = 2 * α + 2 * (-α) * z := by ring
  rw [h1, hexp, Real.exp_add]
  ring
private theorem wrightFisher_right_scale_reflect (α θ₁ θ₂ z : ℝ) :
    selectionMutationScaleDensity α θ₁ θ₂ (1 - z) =
      Real.exp (-2 * α) * selectionMutationScaleDensity (-α) θ₂ θ₁ z := by
  simp only [selectionMutationScaleDensity, mutationScaleDensity]
  have h1 : (1 : ℝ) - (1 - z) = z := by ring
  have hexp : -2 * α * (1 - z) = -2 * α + -2 * (-α) * z := by ring
  rw [h1, hexp, Real.exp_add]
  ring
private theorem wrightFisher_right_const_cancel (u v p q r s : ℝ) (hu : 0 < u)
    (hv : 0 < v) (hrs : r + s = 0) :
    (u ^ (-p) * v ^ (-q) * Real.exp r) * (u ^ p * v ^ q * Real.exp s) = 1 := by
  have e1 : u ^ (-p) * u ^ p = 1 := by rw [← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
  have e2 : v ^ (-q) * v ^ q = 1 := by rw [← Real.rpow_add hv, neg_add_cancel, Real.rpow_zero]
  have e3 : Real.exp r * Real.exp s = 1 := by rw [← Real.exp_add, hrs, Real.exp_zero]
  linear_combination e1 * (v ^ (-q) * Real.exp r * v ^ q * Real.exp s) +
    e2 * (Real.exp r * Real.exp s) + e3
private theorem wrightFisher_right_exp_cancel (α : ℝ) :
    Real.exp (2 * α) * Real.exp (-2 * α) = 1 := by
  have h : (2 : ℝ) * α + -2 * α = 0 := by ring
  rw [← Real.exp_add, h, Real.exp_zero]
private theorem wrightFisher_right_speedInner_explicit (α θ₁ θ₂ c a b : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    (∫ y in a..b, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) =
      (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        (∫ y in a..b, selectionMutationSpeedDensity α θ₁ θ₂ y) := by
  have heq : EqOn
      (fun y => speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y)
      (fun y => (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        selectionMutationSpeedDensity α θ₁ θ₂ y)
      (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    obtain ⟨hay, hyb⟩ := mem_Icc.mp hy
    have hy01 : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha.1 hay, lt_of_le_of_lt hyb hb.2⟩
    exact speedDensityFrom_selectionMutation α θ₁ θ₂ c y hc hy01
  rw [intervalIntegral.integral_congr (μ := volume) heq, intervalIntegral.integral_const_mul]
private theorem wrightFisher_right_scaleInner_explicit (α θ₁ θ₂ c a b : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    (∫ y in a..b, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) =
      (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
        (∫ y in a..b, selectionMutationScaleDensity α θ₁ θ₂ y) := by
  have heq : EqOn
      (fun y => scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y)
      (fun y => (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
        selectionMutationScaleDensity α θ₁ θ₂ y)
      (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    obtain ⟨hay, hyb⟩ := mem_Icc.mp hy
    have hy01 : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha.1 hay, lt_of_le_of_lt hyb hb.2⟩
    exact scaleDensityFrom_selectionMutation α θ₁ θ₂ c y hc hy01
  rw [intervalIntegral.integral_congr (μ := volume) heq, intervalIntegral.integral_const_mul]
private theorem wrightFisher_right_sigma_explicit (α θ₁ θ₂ c a b z : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (∫ y in a..b, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c z =
      (∫ y in a..b, selectionMutationSpeedDensity α θ₁ θ₂ y) *
        selectionMutationScaleDensity α θ₁ θ₂ z := by
  have hinner := wrightFisher_right_speedInner_explicit α θ₁ θ₂ c a b hc ha hb hab
  have houter := scaleDensityFrom_selectionMutation α θ₁ θ₂ c z hc hz
  have h1c : (0 : ℝ) < 1 - c := by linarith [hc.2]
  have hcc := wrightFisher_right_const_cancel c (1 - c) θ₁ θ₂ (-2 * α * c)
    (2 * α * c) hc.1 h1c (by ring)
  rw [hinner, houter]
  linear_combination
    ((∫ y in a..b, selectionMutationSpeedDensity α θ₁ θ₂ y) *
      selectionMutationScaleDensity α θ₁ θ₂ z) * hcc
private theorem wrightFisher_right_scale_explicit (α θ₁ θ₂ c a b z : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (∫ y in a..b, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c z =
      (∫ y in a..b, selectionMutationScaleDensity α θ₁ θ₂ y) *
        selectionMutationSpeedDensity α θ₁ θ₂ z := by
  have hinner := wrightFisher_right_scaleInner_explicit α θ₁ θ₂ c a b hc ha hb hab
  have houter := speedDensityFrom_selectionMutation α θ₁ θ₂ c z hc hz
  have h1c : (0 : ℝ) < 1 - c := by linarith [hc.2]
  have hcc := wrightFisher_right_const_cancel c (1 - c) θ₁ θ₂ (-2 * α * c)
    (2 * α * c) hc.1 h1c (by ring)
  rw [hinner, houter]
  linear_combination
    ((∫ y in a..b, selectionMutationScaleDensity α θ₁ θ₂ y) *
      selectionMutationSpeedDensity α θ₁ θ₂ z) * hcc
private theorem wrightFisher_right_speedInner_subst (α θ₁ θ₂ c x : ℝ) :
    (∫ y in c..x, selectionMutationSpeedDensity α θ₁ θ₂ y) =
      Real.exp (2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ y) := by
  have hc1 : (1 : ℝ) - (1 - c) = c := by ring
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hcomp : (∫ u in (1 - x)..(1 - c),
      selectionMutationSpeedDensity α θ₁ θ₂ (1 - u)) =
      (∫ v in c..x, selectionMutationSpeedDensity α θ₁ θ₂ v) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v => selectionMutationSpeedDensity α θ₁ θ₂ v) 1 (a := 1 - x)
      (b := 1 - c)
    rw [hc1, hx1] at h
    exact h
  have hcongr : (∫ u in (1 - x)..(1 - c),
      selectionMutationSpeedDensity α θ₁ θ₂ (1 - u)) =
      ∫ u in (1 - x)..(1 - c), Real.exp (2 * α) *
        selectionMutationSpeedDensity (-α) θ₂ θ₁ u := by
    apply intervalIntegral.integral_congr
    intro u _
    exact wrightFisher_right_speed_reflect α θ₁ θ₂ u
  have hcm : (∫ u in (1 - x)..(1 - c), Real.exp (2 * α) *
      selectionMutationSpeedDensity (-α) θ₂ θ₁ u) =
      Real.exp (2 * α) *
        (∫ u in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ u) := intervalIntegral.integral_const_mul _ _
  calc (∫ y in c..x, selectionMutationSpeedDensity α θ₁ θ₂ y)
      = (∫ u in (1 - x)..(1 - c),
        selectionMutationSpeedDensity α θ₁ θ₂ (1 - u)) := hcomp.symm
    _ = (∫ u in (1 - x)..(1 - c), Real.exp (2 * α) *
        selectionMutationSpeedDensity (-α) θ₂ θ₁ u) := hcongr
    _ = Real.exp (2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ y) := hcm
private theorem wrightFisher_right_scaleInner_subst (α θ₁ θ₂ c x : ℝ) :
    (∫ y in c..x, selectionMutationScaleDensity α θ₁ θ₂ y) =
      Real.exp (-2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ y) := by
  have hc1 : (1 : ℝ) - (1 - c) = c := by ring
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hcomp : (∫ u in (1 - x)..(1 - c),
      selectionMutationScaleDensity α θ₁ θ₂ (1 - u)) =
      (∫ v in c..x, selectionMutationScaleDensity α θ₁ θ₂ v) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v => selectionMutationScaleDensity α θ₁ θ₂ v) 1 (a := 1 - x)
      (b := 1 - c)
    rw [hc1, hx1] at h
    exact h
  have hcongr : (∫ u in (1 - x)..(1 - c),
      selectionMutationScaleDensity α θ₁ θ₂ (1 - u)) =
      ∫ u in (1 - x)..(1 - c), Real.exp (-2 * α) *
        selectionMutationScaleDensity (-α) θ₂ θ₁ u := by
    apply intervalIntegral.integral_congr
    intro u _
    exact wrightFisher_right_scale_reflect α θ₁ θ₂ u
  have hcm : (∫ u in (1 - x)..(1 - c), Real.exp (-2 * α) *
      selectionMutationScaleDensity (-α) θ₂ θ₁ u) =
      Real.exp (-2 * α) *
        (∫ u in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ u) := intervalIntegral.integral_const_mul _ _
  calc (∫ y in c..x, selectionMutationScaleDensity α θ₁ θ₂ y)
      = (∫ u in (1 - x)..(1 - c),
        selectionMutationScaleDensity α θ₁ θ₂ (1 - u)) := hcomp.symm
    _ = (∫ u in (1 - x)..(1 - c), Real.exp (-2 * α) *
        selectionMutationScaleDensity (-α) θ₂ θ₁ u) := hcongr
    _ = Real.exp (-2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ y) := hcm
private theorem wrightFisher_right_sigma_eq (α θ₁ θ₂ c x : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo c 1) :
    (∫ y in c..x, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x =
      (∫ y in (1 - x)..(1 - c), speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := by
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hc.1 hx.1, hx.2⟩
  have hcx : c ≤ x := le_of_lt hx.1
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hz : (1 : ℝ) - x ∈ Ioo (0 : ℝ) (1 - c) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hz01 : (1 : ℝ) - x ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, lt_trans hz.2 (by linarith [hc.1])⟩
  have hzx : (1 : ℝ) - x ≤ 1 - c := le_of_lt hz.2
  have hstep1 := wrightFisher_right_sigma_explicit α θ₁ θ₂ c c x x hc hc hx01
    hcx hx01
  have hsub := wrightFisher_right_speedInner_subst α θ₁ θ₂ c x
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hrout := wrightFisher_right_scale_reflect α θ₁ θ₂ (1 - x)
  rw [hx1] at hrout
  have hexp := wrightFisher_right_exp_cancel α
  have hstep3 := wrightFisher_right_sigma_explicit (-α) θ₂ θ₁ (1 - c) (1 - x)
    (1 - c) (1 - x) hc' hz01 hc' hzx hz01
  calc (∫ y in c..x, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x
      = (∫ y in c..x, selectionMutationSpeedDensity α θ₁ θ₂ y) *
        selectionMutationScaleDensity α θ₁ θ₂ x := hstep1
    _ = (Real.exp (2 * α) *
          (∫ y in (1 - x)..(1 - c),
            selectionMutationSpeedDensity (-α) θ₂ θ₁ y)) *
        (Real.exp (-2 * α) *
          selectionMutationScaleDensity (-α) θ₂ θ₁ (1 - x)) := by rw [hsub, hrout]
    _ = (∫ y in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ y) *
        selectionMutationScaleDensity (-α) θ₂ θ₁ (1 - x) := by
        linear_combination
          ((∫ y in (1 - x)..(1 - c),
            selectionMutationSpeedDensity (-α) θ₂ θ₁ y) *
            selectionMutationScaleDensity (-α) θ₂ θ₁ (1 - x)) * hexp
    _ = (∫ y in (1 - x)..(1 - c), speedDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := hstep3.symm
private theorem wrightFisher_right_scale_eq (α θ₁ θ₂ c x : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo c 1) :
    (∫ y in c..x, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x =
      (∫ y in (1 - x)..(1 - c), scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := by
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hc.1 hx.1, hx.2⟩
  have hcx : c ≤ x := le_of_lt hx.1
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hz : (1 : ℝ) - x ∈ Ioo (0 : ℝ) (1 - c) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hz01 : (1 : ℝ) - x ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, lt_trans hz.2 (by linarith [hc.1])⟩
  have hzx : (1 : ℝ) - x ≤ 1 - c := le_of_lt hz.2
  have hstep1 := wrightFisher_right_scale_explicit α θ₁ θ₂ c c x x hc hc hx01
    hcx hx01
  have hsub := wrightFisher_right_scaleInner_subst α θ₁ θ₂ c x
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hrout := wrightFisher_right_speed_reflect α θ₁ θ₂ (1 - x)
  rw [hx1] at hrout
  have hexp := wrightFisher_right_exp_cancel α
  have hstep3 := wrightFisher_right_scale_explicit (-α) θ₂ θ₁ (1 - c) (1 - x)
    (1 - c) (1 - x) hc' hz01 hc' hzx hz01
  calc (∫ y in c..x, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x
      = (∫ y in c..x, selectionMutationScaleDensity α θ₁ θ₂ y) *
        selectionMutationSpeedDensity α θ₁ θ₂ x := hstep1
    _ = (Real.exp (-2 * α) *
          (∫ y in (1 - x)..(1 - c),
            selectionMutationScaleDensity (-α) θ₂ θ₁ y)) *
        (Real.exp (2 * α) *
          selectionMutationSpeedDensity (-α) θ₂ θ₁ (1 - x)) := by rw [hsub, hrout]
    _ = (∫ y in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ y) *
        selectionMutationSpeedDensity (-α) θ₂ θ₁ (1 - x) := by
        linear_combination
          ((∫ y in (1 - x)..(1 - c),
            selectionMutationScaleDensity (-α) θ₂ θ₁ y) *
            selectionMutationSpeedDensity (-α) θ₂ θ₁ (1 - x)) * hexp
    _ = (∫ y in (1 - x)..(1 - c), scaleDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := hstep3.symm
private theorem wrightFisher_right_reflection (f : ℝ → ℝ) (c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => f (1 - x)) (Ioo c 1) volume ↔
      IntegrableOn f (Ioo 0 (1 - c)) volume := by
  have h50 : (0 : ℝ) ≤ 1 - c := by linarith [hc.2]
  have h1 : (1 : ℝ) - (1 - c) = c := by ring
  have h2 : (1 : ℝ) - 0 = 1 := by ring
  calc IntegrableOn (fun x => f (1 - x)) (Ioo c 1) volume
      ↔ IntervalIntegrable (fun x => f (1 - x)) volume c 1 :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.2.le).symm
    _ ↔ IntervalIntegrable (fun x => f (1 - x)) volume (1 - (1 - c))
        (1 - 0) := by
        rw [h1, h2]
    _ ↔ IntervalIntegrable f volume (1 - c) 0 :=
        IntervalIntegrable.comp_sub_left_iff 1
    _ ↔ IntervalIntegrable f volume 0 (1 - c) :=
        ⟨IntervalIntegrable.symm, IntervalIntegrable.symm⟩
    _ ↔ IntegrableOn f (Ioo 0 (1 - c)) volume :=
        intervalIntegrable_iff_integrableOn_Ioo_of_le h50

private theorem integrableOn_wrightFisher_right_sigma_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo c 1) volume ↔ θ₂ < 1 := by
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have heq : EqOn
      (fun x => (∫ y in c..x, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x)
      (fun x => (∫ y in (1 - x)..(1 - c), speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x))
      (Ioo c 1) := by
    intro x hx
    exact wrightFisher_right_sigma_eq α θ₁ θ₂ c x hc hx
  have hcong : IntegrableOn
      (fun x => (∫ y in c..x, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x) (Ioo c 1) volume ↔
      IntegrableOn
        (fun x => (∫ y in (1 - x)..(1 - c), speedDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
          scaleDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) (1 - x)) (Ioo c 1) volume :=
    ⟨fun h => h.congr_fun heq measurableSet_Ioo,
      fun h => h.congr_fun heq.symm measurableSet_Ioo⟩
  have hrefl :=
    wrightFisher_right_reflection (fun x => (∫ y in x..(1 - c), speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) x)
      c hc
  have hleft := integrableOn_wrightFisher_left_sigma_iff (-α) θ₂ θ₁ (1 - c) hc'
  exact hcong.trans (hrefl.trans hleft)

private theorem integrableOn_wrightFisher_right_scale_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo c 1) volume ↔ 0 < θ₂ := by
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have heq : EqOn
      (fun x => (∫ y in c..x, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x)
      (fun x => (∫ y in (1 - x)..(1 - c), scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x))
      (Ioo c 1) := by
    intro x hx
    exact wrightFisher_right_scale_eq α θ₁ θ₂ c x hc hx
  have hcong : IntegrableOn
      (fun x => (∫ y in c..x, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x) (Ioo c 1) volume ↔
      IntegrableOn
        (fun x => (∫ y in (1 - x)..(1 - c), scaleDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
          speedDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) (1 - x)) (Ioo c 1) volume :=
    ⟨fun h => h.congr_fun heq measurableSet_Ioo,
      fun h => h.congr_fun heq.symm measurableSet_Ioo⟩
  have hrefl :=
    wrightFisher_right_reflection (fun x => (∫ y in x..(1 - c), scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) x)
      c hc
  have hleft := integrableOn_wrightFisher_left_scale_iff (-α) θ₂ θ₁ (1 - c) hc'
  exact hcong.trans (hrefl.trans hleft)

/-- The Wright-Fisher selection-mutation coefficients, with drift
`(θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))` and diffusion coefficient
`x * (1 - x)`, satisfy the standing hypotheses of Feller's classification at
every interior basepoint `c`, for all real `α`, `θ₁` and `θ₂`. -/
public theorem isFellerAdmissible_selectionMutation (α θ₁ θ₂ c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    IsFellerAdmissible (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c where
  mem_Ioo := hc
  pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
  continuousOn := by fun_prop
  continuousOn_div := ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx =>
    (mul_pos hx.1 (sub_pos.mpr hx.2)).ne'

/-- Wright-Fisher selection-mutation diffusion at `0`: with mutation parameter
`θ₁ = 0`, drift `(θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))` and
diffusion coefficient `x * (1 - x)`, the endpoint `0` is an exit boundary,
for any selection `α`, any `θ₂`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The
conclusion records finiteness of the Feller functionals only. References:
Karlin and Taylor (1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtZero_selectionMutation_exit
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : θ₁ = 0) :
    IsExitBoundaryAtZero
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsExitBoundaryAtZero
  have hSigma := integrableOn_wrightFisher_left_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_left_scale_iff α θ₁ θ₂ c hc
  have h1 : θ₁ < 1 := by rw [hθ]; exact zero_lt_one
  have h2 : ¬ 0 < θ₁ := by rw [hθ]; exact lt_irrefl 0
  exact ⟨isFellerAdmissible_selectionMutation α θ₁ θ₂ c hc,
    hSigma.mpr h1, fun h => h2 (hScale.mp h)⟩

/-- Wright-Fisher selection-mutation diffusion at `0`: with mutation
parameters `0 < θ₁ < 1`, drift as above and diffusion coefficient
`x * (1 - x)`, the endpoint `0` is a regular boundary, for any selection `α`,
any `θ₂`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records
finiteness of the Feller functionals only. References: Karlin and Taylor
(1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtZero_selectionMutation_regular
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ₁ ∧ θ₁ < 1) :
    IsRegularBoundaryAtZero
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsRegularBoundaryAtZero
  have hSigma := integrableOn_wrightFisher_left_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_left_scale_iff α θ₁ θ₂ c hc
  exact ⟨isFellerAdmissible_selectionMutation α θ₁ θ₂ c hc,
    hSigma.mpr hθ.2, hScale.mpr hθ.1⟩

/-- Wright-Fisher selection-mutation diffusion at `0`: with mutation parameter
`1 ≤ θ₁`, drift as above and diffusion coefficient `x * (1 - x)`, the
endpoint `0` is an entrance boundary, for any selection `α`, any `θ₂`, and
any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records finiteness of the
Feller functionals only. References: Karlin and Taylor (1981), Chapter 15
and Ewens (2004), Chapter 4. -/
public theorem boundaryAtZero_selectionMutation_entrance
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : 1 ≤ θ₁) :
    IsEntranceBoundaryAtZero
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsEntranceBoundaryAtZero
  have hSigma := integrableOn_wrightFisher_left_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_left_scale_iff α θ₁ θ₂ c hc
  have h1 : ¬ θ₁ < 1 := not_lt_of_ge hθ
  have h2 : 0 < θ₁ := lt_of_lt_of_le zero_lt_one hθ
  exact ⟨isFellerAdmissible_selectionMutation α θ₁ θ₂ c hc,
    fun h => h1 (hSigma.mp h), hScale.mpr h2⟩

/-- Wright-Fisher selection-mutation diffusion at `1`: with mutation parameter
`θ₂ = 0`, drift `(θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))` and
diffusion coefficient `x * (1 - x)`, the endpoint `1` is an exit boundary,
for any selection `α`, any `θ₁`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The
conclusion records finiteness of the Feller functionals only. References:
Karlin and Taylor (1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtOne_selectionMutation_exit
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : θ₂ = 0) :
    IsExitBoundaryAtOne
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsExitBoundaryAtOne
  have hSigma := integrableOn_wrightFisher_right_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_right_scale_iff α θ₁ θ₂ c hc
  have h1 : θ₂ < 1 := by rw [hθ]; exact zero_lt_one
  have h2 : ¬ 0 < θ₂ := by rw [hθ]; exact lt_irrefl 0
  exact ⟨isFellerAdmissible_selectionMutation α θ₁ θ₂ c hc,
    hSigma.mpr h1, fun h => h2 (hScale.mp h)⟩

/-- Wright-Fisher selection-mutation diffusion at `1`: with mutation
parameters `0 < θ₂ < 1`, drift as above and diffusion coefficient
`x * (1 - x)`, the endpoint `1` is a regular boundary, for any selection `α`,
any `θ₁`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records
finiteness of the Feller functionals only. References: Karlin and Taylor
(1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtOne_selectionMutation_regular
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ₂ ∧ θ₂ < 1) :
    IsRegularBoundaryAtOne
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsRegularBoundaryAtOne
  have hSigma := integrableOn_wrightFisher_right_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_right_scale_iff α θ₁ θ₂ c hc
  exact ⟨isFellerAdmissible_selectionMutation α θ₁ θ₂ c hc,
    hSigma.mpr hθ.2, hScale.mpr hθ.1⟩

/-- Wright-Fisher selection-mutation diffusion at `1`: with mutation parameter
`1 ≤ θ₂`, drift as above and diffusion coefficient `x * (1 - x)`, the
endpoint `1` is an entrance boundary, for any selection `α`, any `θ₁`, and
any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records finiteness of the
Feller functionals only. References: Karlin and Taylor (1981), Chapter 15
and Ewens (2004), Chapter 4. -/
public theorem boundaryAtOne_selectionMutation_entrance
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : 1 ≤ θ₂) :
    IsEntranceBoundaryAtOne
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsEntranceBoundaryAtOne
  have hSigma := integrableOn_wrightFisher_right_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_right_scale_iff α θ₁ θ₂ c hc
  have h1 : ¬ θ₂ < 1 := not_lt_of_ge hθ
  have h2 : 0 < θ₂ := lt_of_lt_of_le zero_lt_one hθ
  exact ⟨isFellerAdmissible_selectionMutation α θ₁ θ₂ c hc,
    fun h => h1 (hSigma.mp h), hScale.mpr h2⟩

end MathlibExt.Biology.PopulationGenetics.Diffusion
