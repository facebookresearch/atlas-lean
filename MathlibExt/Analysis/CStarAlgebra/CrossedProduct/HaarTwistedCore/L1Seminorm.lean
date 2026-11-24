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
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.StarRing
public import MathlibExt.MeasureTheory.Group.HaarWeightedInversion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The original Haar-core L1 ring seminorm

Compact-support Fubini and individual left Haar translations give the literal
coefficient-norm integral its convolution bound. The adopted weighted Haar
inversion formula gives star isometry with the original modular factor.
These are the auxiliary Banach star-algebra data used by the later completion;
no C-star square identity or raw normed ring is imposed on this gauge.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped CompactlySupported Pointwise NNReal

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- The actual left-Haar twisted convolution is submultiplicative for the original L1 gauge. -/
theorem l1Gauge_convolution_le (f g : Carrier μ α) :
    l1Gauge μ α (convolution μ α f g) ≤ l1Gauge μ α f * l1Gauge μ α g := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let F : C_c(G, A) := toCc μ α f
  let Q : C_c(G, A) := toCc μ α g
  let K : G → G → ℝ := fun s t => ‖F t‖ * ‖Q (t⁻¹ * s)‖
  let S : Set G := tsupport F * tsupport Q
  have hScompact : IsCompact S := F.hasCompactSupport.mul Q.hasCompactSupport
  have hSclosed : IsClosed S :=
    (isClosed_tsupport Q).mul_left_of_isCompact F.hasCompactSupport
  have hKcont : Continuous K.uncurry :=
    ((map_continuous F).comp continuous_snd).norm.mul
      (((map_continuous Q).comp (continuous_snd.inv.mul continuous_fst)).norm)
  have hKzeroLeft (s t : G) (ht : t ∉ tsupport F) : K s t = 0 := by
    simp only [K, image_eq_zero_of_notMem_tsupport ht, norm_zero, zero_mul]
  have hKzero (s t : G) (hs : s ∉ S) : K s t = 0 := by
    by_cases ht : t ∈ tsupport F
    · have hq : t⁻¹ * s ∉ tsupport Q := by
        intro hqs
        apply hs
        change s ∈ tsupport F * tsupport Q
        simpa only [mul_inv_cancel_left] using Set.mul_mem_mul ht hqs
      simp only [K, image_eq_zero_of_notMem_tsupport hq, norm_zero, mul_zero]
    · exact hKzeroLeft s t ht
  have hKcomp : HasCompactSupport K.uncurry := by
    refine HasCompactSupport.intro' (hScompact.prod F.hasCompactSupport)
      (hSclosed.prod (isClosed_tsupport F)) ?_
    rintro ⟨s, t⟩ hst
    by_cases hs : s ∈ S
    · exact hKzeroLeft s t (fun ht => hst ⟨hs, ht⟩)
    · exact hKzero s t hs
  have hKslice (s : G) : Integrable (K s) μ := by
    have hc : Continuous (K s) := hKcont.comp (continuous_const.prodMk continuous_id)
    have hcomp : HasCompactSupport (K s) :=
      HasCompactSupport.intro' F.hasCompactSupport (isClosed_tsupport F) (hKzeroLeft s)
    exact hc.integrable_of_hasCompactSupport hcomp
  let J : G → ℝ := fun s => ∫ t : G, K s t ∂μ
  have hJcont : Continuous J := by
    let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
    have hq : IntegrableOn (fun _ : G => (1 : ℝ)) (tsupport F) μ :=
      integrableOn_const F.hasCompactSupport.measure_ne_top
    have hc :=
      _root_.continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        L F.hasCompactSupport hKcont.continuousOn
        (fun s t _ ht => hKzeroLeft s t ht) hq (s := Set.univ)
    have hfun : (fun s : G => ∫ t : G, L (1 : ℝ) (K s t) ∂μ) = J := by
      funext s
      apply integral_congr_ae
      filter_upwards [] with t
      change (1 : ℝ) • K s t = K s t
      exact one_smul ℝ _
    rw [hfun] at hc
    exact continuousOn_univ.mp hc
  have hJzero (s : G) (hs : s ∉ S) : J s = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun t => hKzero s t hs
  have hJcomp : HasCompactSupport J :=
    HasCompactSupport.intro' hScompact hSclosed hJzero
  have hJint : Integrable J μ := hJcont.integrable_of_hasCompactSupport hJcomp
  have hJvalue : (∫ s : G, J s ∂μ) = l1Gauge μ α f * l1Gauge μ α g := by
    calc
      (∫ s : G, J s ∂μ) = ∫ t : G, (∫ s : G, K s t ∂μ) ∂μ :=
        integral_integral_swap_of_hasCompactSupport hKcont hKcomp
      _ = ∫ t : G, ‖F t‖ * l1Gauge μ α g ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        change (∫ s : G, ‖F t‖ * ‖Q (t⁻¹ * s)‖ ∂μ) = ‖F t‖ * l1Gauge μ α g
        rw [integral_const_mul,
          integral_mul_left_eq_self (μ := μ) (fun s : G => ‖Q s‖) t⁻¹]
        rfl
      _ = l1Gauge μ α f * l1Gauge μ α g :=
        integral_mul_const (l1Gauge μ α g) (fun t : G => ‖F t‖)
  have hConvInt : Integrable (fun s : G => ‖convolution μ α f g s‖) μ := by
    change Integrable (fun s : G => ‖ccConvolution μ α F Q s‖) μ
    have hcomp : HasCompactSupport (fun s : G => ‖ccConvolution μ α F Q s‖) :=
      (ccConvolution μ α F Q).hasCompactSupport.comp_left
        (g := fun a : A => ‖a‖) norm_zero
    exact (map_continuous (ccConvolution μ α F Q)).norm.integrable_of_hasCompactSupport hcomp
  have hPoint (s : G) : ‖convolution μ α f g s‖ ≤ J s := by
    change ‖∫ t : G, kernel α F Q s t ∂μ‖ ≤ ∫ t : G, K s t ∂μ
    calc
      ‖∫ t : G, kernel α F Q s t ∂μ‖ ≤ ∫ t : G, ‖kernel α F Q s t‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : G, K s t ∂μ := by
        apply integral_mono (integrable_kernel μ α F Q s).norm (hKslice s)
        intro t
        calc
          ‖kernel α F Q s t‖ ≤ ‖F t‖ * ‖α t (Q (t⁻¹ * s))‖ := norm_mul_le _ _
          _ = K s t := by rw [PointNormCStarAction.norm_apply]
  calc
    l1Gauge μ α (convolution μ α f g) ≤ ∫ s : G, J s ∂μ :=
      integral_mono hConvInt hJint hPoint
    _ = l1Gauge μ α f * l1Gauge μ α g := hJvalue

/-- The original modular involution is isometric for the same auxiliary L1 gauge. -/
@[simp]
theorem l1Gauge_star (f : Carrier μ α) : l1Gauge μ α (star f) = l1Gauge μ α f := by
  have hPoint (s : G) : ‖(star f) s‖ = (Measure.modularCharacter s : ℝ) * ‖f s⁻¹‖ := by
    change ‖crossedStar μ α f s‖ = (Measure.modularCharacter s : ℝ) * ‖f s⁻¹‖
    rw [crossedStar_apply, norm_smul, PointNormCStarAction.norm_apply, norm_star]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (NNReal.coe_nonneg (Measure.modularCharacter s))]
  have hcont : Continuous (fun s : G => ‖f s‖) := (map_continuous (toCc μ α f)).norm
  have hcomp : HasCompactSupport (fun s : G => ‖f s‖) :=
    (toCc μ α f).hasCompactSupport.comp_left (g := fun a : A => ‖a‖) norm_zero
  calc
    l1Gauge μ α (star f) = ∫ s : G, (Measure.modularCharacter s : ℝ) • ‖f s⁻¹‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall hPoint
    _ = l1Gauge μ α f :=
      integral_modularCharacter_smul_inv_of_hasCompactSupport μ hcont hcomp

/-- The original coefficient-norm integral is an actual ring seminorm for Haar convolution. -/
def l1RingSeminorm : RingSeminorm (Carrier μ α) where
  __ := (l1Seminorm μ α).toAddGroupSeminorm
  mul_le' := fun f g => l1Gauge_convolution_le μ α f g

omit [LocallyCompactSpace G] [μ.Regular] in
/-- The auxiliary ring seminorm retains every original coefficient-norm integral value. -/
@[simp]
theorem l1RingSeminorm_apply (f : Carrier μ α) : l1RingSeminorm μ α f = l1Gauge μ α f :=
  rfl

end

end HaarTwistedCore
