/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, the paired `Theorems/Thm_`
and `P2M/Sol/S_` files with stem
`MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists`.
Source: https://github.com/anthropics/fermats-last-theorem
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite double-coset cutoffs

The finite sum of normalized indicators of `sU` is a cutoff for the left
`T`-action when `S` consists of distinct double-coset representatives.
The normalization uses right invariance of the measure on `T`; the weighted
ambient integral uses left invariance. No regularity assumption on the
observable is needed beyond right `U`-invariance.
-/

public section

namespace MeasureTheory

variable {G : Type*} [Group G] (U : Set G) (T : Subgroup G)
  [MeasurableSpace T] (τ : Measure T) (S : Finset G)

/-- Sum of the indicators of `sU`, divided by the real masses of
`T ∩ sUs⁻¹`. The normalization theorem requires those masses to be positive
and finite; at zero or infinite mass this definition is totalized to zero. -/
@[expose] noncomputable def doubleCosetCutoff (y : G) : ℝ :=
  ∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
    (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) y

/-- A finite double-coset cutoff is nonnegative, even before normalization. -/
theorem doubleCosetCutoff_nonneg (y : G) :
    0 ≤ doubleCosetCutoff U T τ S y := by
  exact Finset.sum_nonneg fun s _ =>
    Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr ENNReal.toReal_nonneg) _

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A finite double-coset cutoff for an open set is measurable. -/
theorem measurable_doubleCosetCutoff [MeasurableSpace G] [BorelSpace G]
    (hUo : IsOpen U) : Measurable (doubleCosetCutoff U T τ S) := by
  classical
  exact Finset.measurable_sum _ fun s _ => measurable_const.indicator
    (hUo.preimage (continuous_const.mul continuous_id)).measurableSet

/-- A finite double-coset cutoff for a compact set has compact support. -/
theorem hasCompactSupport_doubleCosetCutoff (hUc : IsCompact U) :
    HasCompactSupport (doubleCosetCutoff U T τ S) := by
  classical
  refine HasCompactSupport.intro (S.isCompact_biUnion fun s _ =>
    (Homeomorph.mulLeft s⁻¹).isCompact_preimage.mpr hUc) fun y hy => ?_
  exact Finset.sum_eq_zero fun s hs =>
    Set.indicator_of_notMem (fun hys => hy (Set.mem_iUnion₂.mpr ⟨s, hs, hys⟩)) _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem doubleCosetCutoff_mul_eq_indicator
    (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (hUinv : ∀ a ∈ U, a⁻¹ ∈ U)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (s₀ : G) (hs₀ : s₀ ∈ S) (t₀ : T) (u₀ : G) (hu₀ : u₀ ∈ U) (t : T) :
    doubleCosetCutoff U T τ S ((t : G) * (t₀ * s₀ * u₀)) =
      ((fun t' : T => t' * t₀) ⁻¹' {t' : T | s₀⁻¹ * (t' : G) * s₀ ∈ U}).indicator
        (fun _ => (τ {t : T | s₀⁻¹ * (t : G) * s₀ ∈ U}).toReal⁻¹) t := by
  classical
  unfold doubleCosetCutoff
  have h0 : ∀ s ∈ S, s ≠ s₀ → {y : G | s⁻¹ * y ∈ U}.indicator
      (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹)
        ((t : G) * (t₀ * s₀ * u₀)) = 0 := by
    intro s hs hne
    refine Set.indicator_of_notMem (fun h => hne ?_) _
    have h' : s⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) ∈ U := h
    exact hS s₀ hs₀ s hs ((t : G) * t₀) (T.mul_mem t.property t₀.property)
      (u₀ * (s⁻¹ * ((t : G) * (t₀ * s₀ * u₀)))⁻¹)
      (hUmul _ hu₀ _ (hUinv _ h')) (by group)
  rw [Finset.sum_eq_single_of_mem s₀ hs₀ h0]
  have he : (s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) ∈ U) ↔
      s₀⁻¹ * ((t : G) * t₀) * s₀ ∈ U := by
    constructor
    · intro h
      have e : s₀⁻¹ * ((t : G) * t₀) * s₀ =
          (s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀))) * u₀⁻¹ := by group
      rw [e]
      exact hUmul _ h _ (hUinv _ hu₀)
    · intro h
      have e : s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) =
          s₀⁻¹ * ((t : G) * t₀) * s₀ * u₀ := by group
      rw [e]
      exact hUmul _ h _ hu₀
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_preimage, Subgroup.coe_mul, he]

/-- The cutoff has integral one on every double coset represented in `S`.
Only right invariance of `τ` is used. The denominator is positive and finite
because its defining conjugate intersection is compact, open, and contains one. -/
theorem integral_doubleCosetCutoff_mul [BorelSpace T]
    [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure]
    (hUo : IsOpen U) (hUc : IsCompact U) (h1U : (1 : G) ∈ U)
    (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (hUinv : ∀ a ∈ U, a⁻¹ ∈ U)
    (hT : IsClosed (T : Set G))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (x : G) (hx : ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∫ t : T, doubleCosetCutoff U T τ S ((t : G) * x) ∂τ = 1 := by
  classical
  obtain ⟨s, hs, t₀, ht₀, u₀, hu₀, rfl⟩ := hx
  have ho : IsOpen {t : T | s⁻¹ * (t : G) * s ∈ U} :=
    hUo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hc : IsCompact {t : T | s⁻¹ * (t : G) * s ∈ U} :=
    hT.isClosedEmbedding_subtypeVal.isCompact_preimage
      (((Homeomorph.mulLeft s⁻¹).trans (Homeomorph.mulRight s)).isCompact_preimage.mpr hUc)
  have hpos : 0 < (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal :=
    ENNReal.toReal_pos (ho.measure_ne_zero τ ⟨1, by simpa using h1U⟩) hc.measure_lt_top.ne
  have he := doubleCosetCutoff_mul_eq_indicator U T τ S hUmul hUinv hS
    s hs (⟨t₀, ht₀⟩ : T) u₀ hu₀
  simp only [he]
  rw [integral_indicator_const _ (ho.measurableSet.preimage (measurable_mul_const _)),
    measureReal_def, measure_preimage_mul_right, smul_eq_mul, mul_inv_cancel₀ hpos.ne']

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem mul_doubleCosetCutoff_eq_sum (ψ : G → ℂ)
    (hψ : ∀ x, ∀ u ∈ U, ψ (x * u) = ψ x) (y : G) :
    ψ y * (doubleCosetCutoff U T τ S y : ℂ) =
      ∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
        (fun _ => ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)) y := by
  classical
  unfold doubleCosetCutoff
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hy : y ∈ {y : G | s⁻¹ * y ∈ U}
  · have hψy : ψ y = ψ s := by simpa only [mul_inv_cancel_left] using hψ s (s⁻¹ * y) hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hψy,
      Complex.ofReal_inv, div_eq_mul_inv]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
      Complex.ofReal_zero, mul_zero]

/-- A right-`U`-invariant observable times the explicit cutoff is integrable,
and its integral is the finite weighted sum. No measurability or boundedness of
`ψ` is assumed. This identity also holds for totalized zero or infinite
intersection masses; only the orbit normalization requires excluding them. -/
theorem doubleCosetCutoff_integrable_and_integral [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (hUo : IsOpen U) (hμUtop : μ U ≠ ⊤)
    (ψ : G → ℂ) (hψ : ∀ x, ∀ u ∈ U, ψ (x * u) = ψ x) :
    Integrable (fun y => ψ y * (doubleCosetCutoff U T τ S y : ℂ)) μ ∧
      ∫ y, ψ y * (doubleCosetCutoff U T τ S y : ℂ) ∂μ =
        ∑ s ∈ S, ψ s * ((μ U).toReal : ℂ) /
          ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ) := by
  classical
  have hA (s : G) : MeasurableSet {y : G | s⁻¹ * y ∈ U} :=
    (hUo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμA (s : G) : μ {y : G | s⁻¹ * y ∈ U} = μ U := measure_preimage_mul μ s⁻¹ U
  have hint : ∀ s ∈ S, Integrable ({y : G | s⁻¹ * y ∈ U}.indicator
      fun _ => ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)) μ := fun s _ =>
    (integrableOn_const (hs := by rwa [hμA s])).integrable_indicator (hA s)
  simp only [mul_doubleCosetCutoff_eq_sum U T τ S ψ hψ]
  refine ⟨integrable_finsetSum S hint, ?_⟩
  rw [integral_finsetSum S hint]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_indicator_const _ (hA s), measureReal_def, hμA s, Complex.real_smul]
  ring

end MeasureTheory
