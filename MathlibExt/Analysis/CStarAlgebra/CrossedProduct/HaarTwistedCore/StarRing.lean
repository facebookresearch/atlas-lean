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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Ring
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Involution
public import Mathlib.Algebra.Star.Module

/-!
# Modular star operation for Haar twisted convolution

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. Writing
δ(s)=Measure.modularCharacter s for the modular character, the involution is
f⁎(s)=δ(s)•α_s(star(f(s⁻¹))). The involution reverses convolution: (f*h)⁎=h⁎*f⁎. With the
additive involution laws this makes the nonunital Haar convolution algebra a star ring.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CompactlySupported CStarAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

omit [μ.Regular] in
/-- **The modular involution reverses convolution.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action. For core coefficients f,h:G→A, twisted
convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. Writing δ(s)=Measure.modularCharacter s
for the modular character, the involution is f⁎(s)=δ(s)•α_s(star(f(s⁻¹))). For compactly
supported continuous core coefficients f,h, crossedStar μ α (f*h)=crossedStar μ α
h*crossedStar μ α f.
-/
theorem crossedStar_convolution (f g : Carrier μ α) :
    crossedStar μ α (convolution μ α f g) =
      convolution μ α (crossedStar μ α g) (crossedStar μ α f) := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let d : G → ℂ := fun r => ((Measure.modularCharacter r : ℝ) : ℂ)
  let S : A →L⋆[ℂ] A := ⟨(starLinearEquiv ℂ).toLinearMap, continuous_star⟩
  let T : A →L[ℂ] A :=
    ⟨LinearMap.ofClass (α.aut s), (StarAlgEquiv.isometry (α.aut s)).continuous⟩
  let J : A →L⋆[ℂ] A := T.comp S
  have hJ (a : A) : J a = α s (star a) := rfl
  have hδ (t : G) : d (s * t) * d t⁻¹ = d s := by
    have h : Measure.modularCharacter (s * t) * Measure.modularCharacter t⁻¹ =
        Measure.modularCharacter s := by
      rw [← map_mul, mul_assoc, mul_inv_cancel, mul_one]
    have hreal : (Measure.modularCharacter (s * t) : ℝ) *
        (Measure.modularCharacter t⁻¹ : ℝ) = (Measure.modularCharacter s : ℝ) := by
      exact_mod_cast h
    change ((Measure.modularCharacter (s * t) : ℝ) : ℂ) *
      ((Measure.modularCharacter t⁻¹ : ℝ) : ℂ) = ((Measure.modularCharacter s : ℝ) : ℂ)
    exact_mod_cast hreal
  have hPoint (t : G) :
      kernel α (toCc μ α (crossedStar μ α g)) (toCc μ α (crossedStar μ α f)) s (s * t) =
        d s • J (kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t) := by
    have hq : (s * t)⁻¹ * s = t⁻¹ := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    have hJkernel : J (kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t) =
        α (s * t) (star (g (s * t)⁻¹)) * α s (star (f t)) := by
      rw [hJ, kernel]
      rw [star_mul, ← PointNormCStarAction.apply_star, PointNormCStarAction.apply_mul_elem,
        ← PointNormCStarAction.apply_mul, mul_inv_rev]
    rw [hJkernel]
    change crossedStar μ α g (s * t) * α (s * t) (crossedStar μ α f ((s * t)⁻¹ * s)) =
      d s • (α (s * t) (star (g (s * t)⁻¹)) * α s (star (f t)))
    rw [crossedStar_apply, crossedStar_apply, hq, inv_inv, PointNormCStarAction.apply_smul]
    change (d (s * t) • α (s * t) (star (g (s * t)⁻¹))) *
      (d t⁻¹ • α (s * t) (α t⁻¹ (star (f t)))) =
        d s • (α (s * t) (star (g (s * t)⁻¹)) * α s (star (f t)))
    have hα : α (s * t) (α t⁻¹ (star (f t))) = α s (star (f t)) := by
      rw [← PointNormCStarAction.apply_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [hα, smul_mul_assoc, mul_smul_comm, ← mul_smul, hδ]
  have hJIntegral :
      (∫ t, J (kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t) ∂μ) =
        J (∫ t, kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t ∂μ) :=
    ContinuousLinearMap.integral_comp_commSL (by intro r z; simp) J
      (integrable_kernel μ α (toCc μ α f) (toCc μ α g) s⁻¹)
  calc
    crossedStar μ α (convolution μ α f g) s =
        d s • J (∫ t, kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t ∂μ) := by
      simp only [crossedStar_apply, convolution_apply, hJ, d, kernel]
    _ = d s • ∫ t, J (kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t) ∂μ :=
      congrArg (fun a : A => d s • a) hJIntegral.symm
    _ = ∫ t, d s • J (kernel α (toCc μ α f) (toCc μ α g) s⁻¹ t) ∂μ :=
      (integral_smul _ _).symm
    _ = ∫ t, kernel α (toCc μ α (crossedStar μ α g))
        (toCc μ α (crossedStar μ α f)) s (s * t) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun t => (hPoint t).symm)
    _ = ∫ r, kernel α (toCc μ α (crossedStar μ α g))
        (toCc μ α (crossedStar μ α f)) s r ∂μ := by
      have he : MeasurableEmbedding (fun t : G => s * t) :=
        (Homeomorph.mulLeft s).measurableEmbedding
      rw [← he.integral_map, map_mul_left_eq_self]
    _ = convolution μ α (crossedStar μ α g) (crossedStar μ α f) s := by
      simp only [convolution_apply, kernel]

/-- **Star ring of Haar twisted core coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. Writing
δ(s)=Measure.modularCharacter s for the modular character, the involution is
f⁎(s)=δ(s)•α_s(star(f(s⁻¹))). These operations make Carrier μ α a star ring, with
star(f*h)=star(h)*star(f).
-/
instance instStarRingCarrier : StarRing (Carrier μ α) where
  star_mul := crossedStar_convolution μ α
  star_add := crossedStar_add μ α

end

end HaarTwistedCore
