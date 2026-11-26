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
# The L¹ gauge of compactly supported coefficients

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a compactly supported
continuous coefficient f:G→A, write q(f)=∫ s, ‖f(s)‖ ∂μ. This gauge is nonnegative and
satisfies q(c•f)=‖c‖q(f) and q(-f)=q(f). If G has its Borel measurable structure and μ is
finite on compact sets, then q(f+h)≤q(f)+q(h), so q is a complex seminorm on the coefficient
core. When the integrand is not integrable, the real Bochner integral has value zero.
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

/-- **Integral of the coefficient norm.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a compactly supported
continuous coefficient f:G→A, write q(f)=∫ s, ‖f(s)‖ ∂μ. The real-valued function l1Gauge μ α
f is q(f), using the C-star norm on A. When the integrand is not integrable, the real Bochner
integral has value zero.
-/
def l1Gauge (f : Carrier μ α) : ℝ :=
  ∫ s : G, ‖f s‖ ∂μ

/-- **Nonnegativity of the L¹ gauge.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For every compactly supported
continuous coefficient f:G→A, 0≤l1Gauge μ α f=∫ s, ‖f(s)‖ ∂μ.
-/
theorem l1Gauge_nonneg (f : Carrier μ α) : 0 ≤ l1Gauge μ α f :=
  integral_nonneg fun _ => norm_nonneg _

/-- **L¹ gauge of the zero coefficient.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The zero function in Carrier μ α
has l1Gauge μ α 0=∫ s, ‖0‖ ∂μ=0.
-/
@[simp]
theorem l1Gauge_zero : l1Gauge μ α (0 : Carrier μ α) = 0 := by
  simp only [l1Gauge, toCc_zero, CompactlySupportedContinuousMap.zero_apply, norm_zero,
    integral_zero]

/-- **Complex scaling of the L¹ gauge.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a compactly supported
continuous coefficient f:G→A, write q(f)=∫ s, ‖f(s)‖ ∂μ. For c∈ℂ, q(c•f)=‖c‖q(f).
-/
theorem l1Gauge_smul (c : ℂ) (f : Carrier μ α) :
    l1Gauge μ α (c • f) = ‖c‖ * l1Gauge μ α f := by
  have hfun : (fun s : G => ‖(c • f) s‖) = fun s : G => ‖c‖ * ‖f s‖ := by
    funext s
    rw [toCc_smul, CompactlySupportedContinuousMap.smul_apply, norm_smul]
  unfold l1Gauge
  rw [hfun, integral_const_mul]

/-- **L¹ gauge of the additive inverse.**

Let G be a monoid with a topology and measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a compactly supported
continuous coefficient f:G→A, write q(f)=∫ s, ‖f(s)‖ ∂μ. Taking pointwise negatives preserves
the gauge: q(-f)=q(f).
-/
@[simp]
theorem l1Gauge_neg (f : Carrier μ α) : l1Gauge μ α (-f) = l1Gauge μ α f := by
  rw [← neg_one_smul ℂ f, l1Gauge_smul, norm_neg, norm_one, one_mul]

variable [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

omit [Monoid G] in
/-- **Integrability of the compact coefficient norm.**

Let G be a topological space with its Borel measurable structure, μ a measure finite on
compact sets and A a nonunital complex C-star algebra. For every compactly supported
continuous f:G→A, the real-valued function s↦‖f(s)‖ is μ-integrable.
-/
private theorem l1NormIntegrable (f : C_c(G, A)) :
    Integrable (fun s : G => ‖f s‖) μ := by
  have hcomp : HasCompactSupport (fun s : G => ‖f s‖) :=
    f.hasCompactSupport.comp_left (g := fun a : A => ‖a‖) norm_zero
  exact (map_continuous f).norm.integrable_of_hasCompactSupport hcomp

/-- **Triangle inequality for the L¹ gauge.**

Let G be a monoid with a Borel topology, μ a measure finite on compact sets, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a compactly supported
continuous coefficient f:G→A, write q(f)=∫ s, ‖f(s)‖ ∂μ. For core coefficients f,h,
q(f+h)≤q(f)+q(h).
-/
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

/-- **Complex L¹ seminorm on the coefficient core.**

Let G be a monoid with a Borel topology, μ a measure finite on compact sets, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The complex seminorm l1Seminorm μ
α on Carrier μ α has value q(f)=∫ s, ‖f(s)‖ ∂μ for each compactly supported continuous
coefficient f.
-/
def l1Seminorm : Seminorm ℂ (Carrier μ α) :=
  Seminorm.of (l1Gauge μ α) (l1Gauge_add_le μ α) (l1Gauge_smul μ α)

/-- **Value of the complex L¹ seminorm.**

Let G be a monoid with a Borel topology, μ a measure finite on compact sets, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For every f∈Carrier μ α,
l1Seminorm μ α f=l1Gauge μ α f=∫ s, ‖f(s)‖ ∂μ.
-/
@[simp]
theorem l1Seminorm_apply (f : Carrier μ α) : l1Seminorm μ α f = l1Gauge μ α f :=
  rfl

end

end HaarTwistedCore
