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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The original Haar-core L1 gauge

The auxiliary gauge is the integral of the norm of the original compactly
supported coefficient function. It uses the original coefficient norm and
complex module; no norm or metric is installed on the raw Haar core.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CompactlySupported

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- The literal integral of the original coefficient norm on the indexed Haar core. -/
def l1Gauge (f : Carrier μ α) : ℝ :=
  ∫ s : G, ‖f s‖ ∂μ

/-- The original coefficient-norm integral is nonnegative. -/
theorem l1Gauge_nonneg (f : Carrier μ α) : 0 ≤ l1Gauge μ α f :=
  integral_nonneg fun _ => norm_nonneg _

/-- The indexed zero coefficient function has zero auxiliary L1 gauge. -/
@[simp]
theorem l1Gauge_zero : l1Gauge μ α (0 : Carrier μ α) = 0 := by
  simp only [l1Gauge, toCc_zero, CompactlySupportedContinuousMap.zero_apply, norm_zero,
    integral_zero]

/-- Original complex coefficient scaling multiplies the gauge by the scalar norm. -/
theorem l1Gauge_smul (c : ℂ) (f : Carrier μ α) :
    l1Gauge μ α (c • f) = ‖c‖ * l1Gauge μ α f := by
  have hfun : (fun s : G => ‖(c • f) s‖) = fun s : G => ‖c‖ * ‖f s‖ := by
    funext s
    rw [toCc_smul, CompactlySupportedContinuousMap.smul_apply, norm_smul]
  unfold l1Gauge
  rw [hfun, integral_const_mul]

/-- Taking the additive inverse preserves the same coefficient-norm integral. -/
@[simp]
theorem l1Gauge_neg (f : Carrier μ α) : l1Gauge μ α (-f) = l1Gauge μ α f := by
  rw [← neg_one_smul ℂ f, l1Gauge_smul, norm_neg, norm_one, one_mul]

variable [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

omit [Monoid G] in
/-- The norm of a genuine compactly supported continuous coefficient is integrable. -/
private theorem l1NormIntegrable (f : C_c(G, A)) :
    Integrable (fun s : G => ‖f s‖) μ := by
  have hcomp : HasCompactSupport (fun s : G => ‖f s‖) :=
    f.hasCompactSupport.comp_left (g := fun a : A => ‖a‖) norm_zero
  exact (map_continuous f).norm.integrable_of_hasCompactSupport hcomp

/-- The original additive coefficient functions satisfy the L1 triangle inequality. -/
theorem l1Gauge_add_le (f g : Carrier μ α) :
    l1Gauge μ α (f + g) ≤ l1Gauge μ α f + l1Gauge μ α g := by
  have hf := l1NormIntegrable μ (toCc μ α f)
  have hg := l1NormIntegrable μ (toCc μ α g)
  have hfg := l1NormIntegrable μ (toCc μ α (f + g))
  have hpoint (s : G) : ‖(f + g) s‖ ≤ ‖f s‖ + ‖g s‖ := by
    rw [toCc_add, CompactlySupportedContinuousMap.add_apply]
    exact norm_add_le _ _
  calc
    l1Gauge μ α (f + g) ≤ ∫ s : G, (‖f s‖ + ‖g s‖) ∂μ :=
      integral_mono hfg (hf.add hg) hpoint
    _ = l1Gauge μ α f + l1Gauge μ α g := integral_add hf hg

/-- The literal coefficient-norm integral is an actual complex seminorm on the same raw core. -/
def l1Seminorm : Seminorm ℂ (Carrier μ α) :=
  Seminorm.of (l1Gauge μ α) (l1Gauge_add_le μ α) (l1Gauge_smul μ α)

/-- The complex seminorm retains the exact original coefficient-norm integral. -/
@[simp]
theorem l1Seminorm_apply (f : Carrier μ α) : l1Seminorm μ α f = l1Gauge μ α f :=
  rfl

end

end HaarTwistedCore
