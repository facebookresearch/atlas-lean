/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, the paired `Theorems/Thm_` and
`P2M/Sol/S_` files with stem:
`MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact`.
Source: https://github.com/anthropics/fermats-last-theorem
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import MathlibExt.MeasureTheory.Group.BruhatSection
import MathlibExt.MeasureTheory.Group.CutoffIndependence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive common integral of cocompact subgroup cutoffs

For a closed cocompact subgroup with inversion-invariant Haar measure,
normalized nonnegative measurable compactly supported cutoffs have a common
positive integral. A continuous such cutoff exists. The arbitrary measurable
cutoffs need not be bounded: their integrability comes from the normalized
cutoff estimate, not from compact support alone.

This theorem does not identify the common integral with a quotient measure.
-/

public section

open scoped Pointwise

namespace MeasureTheory

/-- **Positive common integral of cocompact subgroup cutoffs.**
A compact cocompactness witness gives a continuous normalized cutoff and
a positive common integral for all nonnegative measurable compactly supported
normalized cutoffs. Every such cutoff is genuinely integrable, even when it
is not bounded. Neither the ambient group nor the subgroup must be Hausdorff. -/
theorem exists_pos_integral_cutoff_of_cocompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T)
    [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ t : T, ∃ k ∈ K, x = (t : G) * k) :
    ∃ κ : ℝ, 0 < κ ∧
      (∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
        ∀ x, ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∀ w : G → ℝ, (∀ x, 0 ≤ w x) → Measurable w → HasCompactSupport w →
        (∀ x, ∫ t : T, w ((t : G) * x) ∂τ = 1) →
        Integrable w μ ∧ ∫ x, w x ∂μ = κ := by
  have : τ.IsMulRightInvariant := by
    have hi := (inferInstance : τ.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at hi
  have hcover : Set.univ ⊆ (T : Set G) * K := by
    intro x _
    obtain ⟨t, k, hk, rfl⟩ := hcov x
    exact ⟨t, t.2, k, hk, rfl⟩
  obtain ⟨β, hβc, hβs, hβ0, hβ1⟩ :=
    exists_continuous_cutoff_of_subset_mul T hT τ hK hcover
  have hβnorm : ∀ x, ∫ t : T, β ((t : G) * x) ∂τ = 1 :=
    fun x => hβ1 x (Set.mem_univ x)
  refine ⟨∫ x, β x ∂μ, ?_, ⟨β, hβ0, hβc, hβs, hβnorm⟩, ?_⟩
  · have hne : ∃ x, β x ≠ 0 := by
      by_contra h
      push Not at h
      have hn := hβnorm 1
      simp [h] at hn
    obtain ⟨x, hx⟩ := hne
    exact hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hβs hβ0 hx
  · intro w hw0 hwm hws hw1
    have hi := integrable_mul_of_integral_subgroup_translate_eq_one T μ τ hT
      (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => by simp⟩
      (fun _ _ => rfl) w hw0 hwm hws (fun x _ => hw1 x)
    have heq := integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
      T hT μ τ (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => by simp⟩
      (fun _ _ => rfl) w β
      ⟨hw0, hwm, hws, fun x _ => hw1 x⟩
      ⟨hβ0, hβc.measurable, hβs, fun x _ => hβnorm x⟩
    simp only [one_mul] at hi heq
    refine ⟨?_, ?_⟩
    · simpa using hi.re
    · rw [integral_complex_ofReal, integral_complex_ofReal] at heq
      exact Complex.ofReal_injective heq

end MeasureTheory
