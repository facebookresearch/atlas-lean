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
# L¹ continuity of twisted left translations

Let G be a locally compact Borel topological group, A a nonunital complex C-star algebra, α a
point-norm action and μ a measure finite on compact sets. For f:G→A compactly supported and
continuous, put L_g f(s)=α_g(f(g⁻¹*s)) and q(k)=∫ s, ‖k(s)‖ ∂μ. The function g↦q(L_g f-f) is
continuous and tends to zero as g→1. If μ is left Haar, then q(L_g f)=q(f).
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
/-- **Left Haar translations preserve the L¹ gauge.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action. For g∈G and a compactly supported continuous coefficient f,
put L_g f(s)=α_g(f(g⁻¹*s)). Then ∫ s, ‖L_g f(s)‖ ∂μ=∫ s, ‖f(s)‖ ∂μ.
-/
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

/-- **Continuity of the L¹ translation distance.**

Let G be a locally compact Borel topological group, μ a measure finite on compact sets, A a
nonunital complex C-star algebra and α a point-norm action. For f:G→A compactly supported and
continuous, the function g↦∫ s, ‖α_g(f(g⁻¹*s))-f(s)‖ ∂μ is continuous.
-/
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

/-- **Twisted translations approach the identity in L¹.**

Let G be a locally compact Borel topological group, μ a measure finite on compact sets, A a
nonunital complex C-star algebra and α a point-norm action. For every compactly supported
continuous f:G→A, ∫ s, ‖α_g(f(g⁻¹*s))-f(s)‖ ∂μ tends to 0 as g tends to the group identity.
-/
theorem tendsto_l1Gauge_groupLeft_sub (f : Carrier μ α) :
    Tendsto (fun g : G => l1Gauge μ α (groupLeft μ α g f - f)) (𝓝 1) (𝓝 0) := by
  simpa only [groupLeft_one, LinearMap.id_apply, sub_self, l1Gauge_zero] using
    (continuous_l1Gauge_groupLeft_sub μ α f).tendsto (1 : G)

end

end HaarTwistedCore
