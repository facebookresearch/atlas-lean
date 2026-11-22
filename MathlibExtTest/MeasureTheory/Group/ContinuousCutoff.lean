/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Group.BruhatSection
import MathlibExt.MeasureTheory.Group.CutoffIndependence
import MathlibExt.MeasureTheory.Group.CutoffMass
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
Exact source-type consumers for the five frozen continuous/bounded cutoff
statements, plus applications to harmonic integration and normalized weights.
The exact tests deliberately retain the original assumptions, including the
absence of T2 in the second and fourth statements and only first countability
in the third. Source hashes and the full clause map are in the port evidence.
-/

open MeasureTheory
open scoped Pointwise

universe u

namespace ContinuousCutoffTest

-- Source 1: a general homomorphism, not just subgroup inclusion; H, not G,
-- is second countable. The original universes are Type 0.
example {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (τ : Measure H) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (ι : H →* G) (hι : Topology.IsClosedEmbedding ι)
    (K : Set G) (hK : IsCompact K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ g, 0 ≤ w g) ∧
      ∀ (h : H) (k : G), k ∈ K → ∫ h', w (ι h' * (ι h * k)) ∂τ = 1 :=
  exists_continuous_cutoff_of_isClosedEmbedding τ ι hι K hK

-- Source 2: no T2, inversion invariance rather than right invariance,
-- and normalization on EVERY orbit, not just points in the compact set.
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (S : Subgroup G) (hS : IsClosed (S : Set G))
    [MeasurableSpace S] [BorelSpace S]
    (τ : Measure S) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ s : S, ∃ k ∈ K, x = (s : G) * k) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
      ∀ x : G, ∫ s : S, w ((s : G) * x) ∂τ = 1 := by
  have : τ.IsMulRightInvariant := by
    have hi := (inferInstance : τ.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at hi
  have hc : Set.univ ⊆ (S : Set G) * K := by
    intro x _
    obtain ⟨s, k, hk, rfl⟩ := hcov x
    exact ⟨s, s.2, k, hk, rfl⟩
  obtain ⟨w, hwc, hws, hw0, hw1⟩ := exists_continuous_cutoff_of_subset_mul S hS τ hK hc
  exact ⟨w, hwc, hws, hw0, fun x => hw1 x (Set.mem_univ x)⟩

-- Source 3: no second-countability or compact-open-subgroup assumption.
example {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [FirstCountableTopology G]
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) →
        ∫ t : T, w (t * x) ∂τ = 1 := by
  have : τ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have heq : (fun x : T => x * g) = fun x : T => g * x :=
      funext fun x => Subtype.ext (hcomm x x.2 g g.2)
    rw [heq]
    exact map_mul_left_eq_self τ g
  obtain ⟨w, hwc, hws, hw0, hw1⟩ :=
    exists_continuous_cutoff_of_subset_mul T hT τ hΩ (Set.Subset.refl _)
  refine ⟨w, hwc, hw0, hws, ?_⟩
  rintro x ⟨t, ht, d, hd, rfl⟩
  exact hw1 _ ⟨t, ht, d, hd, rfl⟩

-- Source 4: the global bound is obtained from continuity, not from mere
-- measurability and compact support. No separation assumption is added.
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T)
    [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ W : G → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable W ∧ HasCompactSupport W ∧
      (∃ B : ℝ, ∀ x, W x ≤ B) ∧
      ∀ x : G, (∃ t : T, ∃ k ∈ Ω, x = (t : G) * k) →
        ∫ t : T, W ((t : G) * x) ∂τ = 1 := by
  obtain ⟨w, hwc, hws, hw0, hw1⟩ :=
    exists_continuous_cutoff_of_subset_mul T hT τ hΩ (Set.Subset.refl _)
  obtain ⟨B, hB⟩ := hwc.bounded_above_of_compact_support hws
  refine ⟨w, hw0, hwc.measurable, hws, ⟨B, fun x => ?_⟩, ?_⟩
  · exact (le_abs_self _).trans (hB x)
  · rintro x ⟨t, k, hk, rfl⟩
    exact hw1 _ ⟨t, t.2, k, hk, rfl⟩

-- Source 5: positivity, one continuous witness, and equality for ALL
-- measurable normalized cutoffs, without adding boundedness to those cutoffs.
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
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
        (∀ x, ∫ t : T, w ((t : G) * x) ∂τ = 1) → ∫ x, w x ∂μ = κ := by
  obtain ⟨κ, hκ, hw, hall⟩ := exists_pos_integral_cutoff_of_cocompact T hT μ τ K hK hcov
  exact ⟨κ, hκ, hw, fun w hw0 hwm hws hw1 => (hall w hw0 hwm hws hw1).2⟩

-- Empty K is allowed. No normalization is imposed on an empty saturation.
example {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (τ : Measure H)
    [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure] [τ.IsMulRightInvariant]
    (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
      ∀ (h : H) (k : G), k ∈ (∅ : Set G) →
        ∫ h', w (ι h' * (ι h * k)) ∂τ = 1 :=
  exists_continuous_cutoff_of_isClosedEmbedding τ ι hι ∅ isCompact_empty

-- Nonempty normalization cannot be witnessed by the zero function.
example {G H : Type*} [Group G] [Group H] [MeasurableSpace H]
    (τ : Measure H) (ι : H →* G) (K : Set G) (hK : K.Nonempty) :
    ¬ (∀ (h : H) (k : G), k ∈ K →
      ∫ h' : H, (0 : G → ℝ) (ι h' * (ι h * k)) ∂τ = 1) := by
  intro hz
  obtain ⟨k, hk⟩ := hK
  simpa using hz 1 k hk

-- The positive denominator floor, including the zero-average boundary.
example (a m : ℝ) (hm : 0 < m) : 0 < max a m := lt_max_of_lt_right hm
example (m : ℝ) : (0 : ℝ) / max 0 m = 0 := zero_div _

-- Connected nondiscrete application: compactly supported averaging kernels
-- on the real additive group, expressed through the standard type tag.
namespace RealLine

local instance : MeasurableSpace (Multiplicative ℝ) := borel _
local instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

example : ∃ w : Multiplicative ℝ → ℝ,
    Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
    ∀ x, ∫ t : Multiplicative ℝ, w (t * x) ∂Measure.haar = 1 := by
  obtain ⟨w, hwc, hws, hw0, hw1⟩ :=
    exists_continuous_cutoff_of_isClosedEmbedding
      (Measure.haar : Measure (Multiplicative ℝ)) (MonoidHom.id (Multiplicative ℝ))
      Topology.IsClosedEmbedding.id {1} isCompact_singleton
  refine ⟨w, hwc, hws, hw0, fun x => ?_⟩
  simpa using hw1 x 1 (Set.mem_singleton 1)

end RealLine

-- Harmonic integration: an invariant observable supported in a compact
-- saturation has a genuinely integrable continuous normalized weight.
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T)
    [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (K : Set G) (hK : IsCompact K) (hFK : Function.support F ⊆ (T : Set G) * K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
      (∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      Integrable (fun x => F x * (w x : ℂ)) μ := by
  have : τ.IsMulRightInvariant := by
    have hi := (inferInstance : τ.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at hi
  obtain ⟨w, hwc, hws, hw0, hw1⟩ := exists_continuous_cutoff_of_subset_mul T hT τ hK hFK
  exact ⟨w, hwc, hws, hw0, hw1,
    integrable_mul_of_integral_subgroup_translate_eq_one T μ τ hT
      F hFm hFb hFT w hw0 hwc.measurable hws hw1⟩

-- Normalize a cocompact cutoff to total integral one while retaining its
-- explicitly scaled orbit integral. This produces continuous probability
-- weights without pretending the common integral is a quotient measure.
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T)
    [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ t : T, ∃ k ∈ K, x = (t : G) * k) :
    ∃ (κ : ℝ) (p : G → ℝ), 0 < κ ∧ Continuous p ∧ HasCompactSupport p ∧
      (∀ x, 0 ≤ p x) ∧ Integrable p μ ∧ (∫ x, p x ∂μ = 1) ∧
      ∀ x, ∫ t : T, p ((t : G) * x) ∂τ = κ⁻¹ := by
  obtain ⟨κ, hκ, ⟨w, hw0, hwc, hws, hw1⟩, hall⟩ :=
    exists_pos_integral_cutoff_of_cocompact T hT μ τ K hK hcov
  obtain ⟨hi, heq⟩ := hall w hw0 hwc.measurable hws hw1
  refine ⟨κ, fun x => w x / κ, hκ, hwc.div_const κ, ?_,
    fun x => div_nonneg (hw0 x) hκ.le, hi.div_const κ, ?_, ?_⟩
  · exact hws.mono fun x hx hw => hx (by simp [hw])
  · rw [integral_div, heq, div_self hκ.ne']
  · intro x
    rw [integral_div, hw1, one_div]

end ContinuousCutoffTest
