/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Group.LocallyConstantCutoff
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.ZMod

/-! # Consumers and boundary checks for normalized subgroup cutoffs -/

open MeasureTheory Set

set_option autoImplicit false

section Averaging

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K : Set G))
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]

/-- The cutoff defines an averaging operator that fixes every invariant
real-valued function on the saturation of the compact set. -/
example (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
      HasCompactSupport w ∧ ∀ x : G,
      (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) →
      Integrable (fun t : T => w ((t : G) * x)) τ ∧
      ∀ f : G → ℝ, (∀ (t : T) y, f ((t : G) * y) = f y) →
        ∫ t : T, w ((t : G) * x) * f ((t : G) * x) ∂τ = f x := by
  obtain ⟨w, hwn, hwl, hwc, hw⟩ :=
    exists_isLocallyConstant_integral_subgroup_mul_eq_one
      K hK hK' T hT hcomm τ Ω hΩ
  refine ⟨w, hwn, hwl, hwc, fun x hx => ?_⟩
  refine ⟨integrable_of_integral_eq_one (hw x hx), fun f hf => ?_⟩
  simp_rw [hf]
  rw [integral_mul_const, hw x hx, one_mul]

/-- Empty saturation imposes no normalization condition; all other
properties still apply to the same witness. -/
example : ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
    HasCompactSupport w := by
  obtain ⟨w, hn, hl, hc, -⟩ :=
    exists_isLocallyConstant_integral_subgroup_mul_eq_one
      K hK hK' T hT hcomm τ ∅ isCompact_empty
  exact ⟨w, hn, hl, hc⟩

end Averaging

namespace TwoInfiniteOrbits

private abbrev G := Multiplicative ℤ × Multiplicative (ZMod 2)

private abbrev T : Subgroup G :=
  (MonoidHom.snd (Multiplicative ℤ) (Multiplicative (ZMod 2))).ker

local instance : MeasurableSpace T := borel T
local instance : BorelSpace T := ⟨rfl⟩
local instance : (Measure.count : Measure T).IsHaarMeasure where
  lt_top_of_isCompact _ h := Measure.count_apply_lt_top.mpr h.finite_of_discrete
  toIsMulLeftInvariant := inferInstance
  open_pos _ _ h := Measure.count_ne_zero_iff.mpr h

/-- On `ℤ × (ℤ/2ℤ)`, one finitely supported function simultaneously has
counting integral one on both infinite orbits of the first factor. In
particular, neither a zero witness nor a nonintegrable witness passes. -/
example : ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
    (Function.support w).Finite ∧ w ≠ 0 ∧
      ∀ x : G, Integrable (fun t : T => w ((t : G) * x)) Measure.count ∧
        ∫ t : T, w ((t : G) * x) ∂Measure.count = 1 := by
  let Ω : Set G := ({1} : Set (Multiplicative ℤ)) ×ˢ Set.univ
  have hΩ : IsCompact Ω := isCompact_singleton.prod isCompact_univ
  have hcover (x : G) : ∃ t ∈ T, ∃ d ∈ Ω, x = t * d := by
    refine ⟨(x.1, 1), ?_, (1, x.2), ⟨rfl, mem_univ _⟩, ?_⟩
    · change (1 : Multiplicative (ZMod 2)) = 1
      rfl
    · simp
  obtain ⟨w, hn, hl, hc, hw⟩ :=
    exists_isLocallyConstant_integral_subgroup_mul_eq_one
      (⊥ : Subgroup G) (by simp) (isOpen_discrete _)
      T (isClosed_discrete _) (fun s _ t _ => mul_comm s t)
      Measure.count Ω hΩ
  have hnorm (x : G) : ∫ t : T, w ((t : G) * x) ∂Measure.count = 1 :=
    hw x (hcover x)
  refine ⟨w, hn, hl, ?_, ?_, fun x =>
    ⟨integrable_of_integral_eq_one (hnorm x), hnorm x⟩⟩
  · exact hc.isCompact.finite_of_discrete.subset (subset_tsupport w)
  · intro hz
    have h := hnorm 1
    simp only [hz, Pi.zero_apply, integral_zero] at h
    exact zero_ne_one h

end TwoInfiniteOrbits

/-- Without the compact-open-subgroup hypothesis, the conclusion need not
hold: every compactly supported locally constant function on `ℝ` is zero. -/
example (w : ℝ → ℝ) (hl : IsLocallyConstant w) (hc : HasCompactSupport w) :
    w = 0 := by
  have hz : w 0 = 0 := by
    by_contra hn
    have hs : tsupport w = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      apply subset_tsupport w
      change w x ≠ 0
      rwa [hl.apply_eq_of_preconnectedSpace x 0]
    exact noncompact_univ ℝ (hs ▸ hc.isCompact)
  ext x
  exact (hl.apply_eq_of_preconnectedSpace x 0).trans hz
