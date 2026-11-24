/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Gauge
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# L1 continuity of the original compact-support group translates

The literal inverse left translate with the coefficient action preserves the
Haar coefficient integral. On a compact neighborhood of each group element,
all translated supports lie in one compact set. Joint point-norm continuity
and the support-local integral continuity theorem give the L1 orbit limit.
This supplies a strict continuity prerequisite for the actual covariant group
representation; no normed or C-star structure is installed on the raw core.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped CompactlySupported Pointwise Topology

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

section HaarIsometry

variable [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] in
/-- The original inverse left translate is isometric for the literal Haar L1 gauge. -/
theorem l1Gauge_groupLeft (g : G) (f : Carrier μ α) :
    l1Gauge μ α (groupLeft μ α g f) = l1Gauge μ α f := by
  calc
    l1Gauge μ α (groupLeft μ α g f) = ∫ s : G, ‖f (g⁻¹ * s)‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        change ‖(toCc μ α (groupLeft μ α g f)) s‖ = ‖(toCc μ α f) (g⁻¹ * s)‖
        rw [groupLeft_apply, PointNormCStarAction.norm_apply]
    _ = l1Gauge μ α f := integral_mul_left_eq_self (μ := μ) (fun s : G => ‖f s‖) g⁻¹

end HaarIsometry

variable [IsFiniteMeasureOnCompacts μ]

/-- The original compact translates vary continuously in the coefficient-integral distance. -/
theorem continuous_l1Gauge_groupLeft_sub (f : Carrier μ α) :
    Continuous fun g : G => l1Gauge μ α (groupLeft μ α g f - f) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨V, hVcompact, hVnhds⟩ := exists_compact_mem_nhds g₀
  let F : C_c(G, A) := toCc μ α f
  let K : Set G := (V * tsupport F) ∪ tsupport F
  have hKcompact : IsCompact K := (hVcompact.mul F.hasCompactSupport).union F.hasCompactSupport
  let D : G → G → ℝ := fun g s => ‖α g (F (g⁻¹ * s)) - F s‖
  have hDcont : Continuous D.uncurry :=
    ((α.continuous_apply continuous_fst
      ((map_continuous F).comp (continuous_fst.inv.mul continuous_snd))).sub
        ((map_continuous F).comp continuous_snd)).norm
  have hDzero (g s : G) (hg : g ∈ V) (hs : s ∉ K) : D g s = 0 := by
    have hFzero : F s = 0 := image_eq_zero_of_notMem_tsupport fun hfs => hs (Or.inr hfs)
    have hTransZero : F (g⁻¹ * s) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hfs
      apply hs
      apply Or.inl
      simpa only [mul_inv_cancel_left] using Set.mul_mem_mul hg hfs
    simp only [D, hFzero, hTransZero, PointNormCStarAction.apply_zero, sub_self, norm_zero]
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hOne : IntegrableOn (fun _ : G => (1 : ℝ)) K μ :=
    integrableOn_const hKcompact.measure_ne_top
  have hIntegral :=
    _root_.continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
      L hKcompact hDcont.continuousOn hDzero hOne
  have hfun : (fun g : G => ∫ s : G, L (1 : ℝ) (D g s) ∂μ) =
      fun g : G => l1Gauge μ α (groupLeft μ α g f - f) := by
    funext g
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      change (1 : ℝ) • ‖α g (f (g⁻¹ * s)) - f s‖ = ‖α g (f (g⁻¹ * s)) - f s‖
      exact one_smul ℝ _
  rw [hfun] at hIntegral
  exact (hIntegral g₀ (mem_of_mem_nhds hVnhds)).continuousAt hVnhds

/-- The literal coefficient-integral distance of a translate from its source tends to zero at one. -/
theorem tendsto_l1Gauge_groupLeft_sub (f : Carrier μ α) :
    Tendsto (fun g : G => l1Gauge μ α (groupLeft μ α g f - f)) (𝓝 1) (𝓝 0) := by
  simpa only [groupLeft_one, LinearMap.id_apply, sub_self, l1Gauge_zero] using
    (continuous_l1Gauge_groupLeft_sub μ α f).tendsto (1 : G)

end

end HaarTwistedCore
