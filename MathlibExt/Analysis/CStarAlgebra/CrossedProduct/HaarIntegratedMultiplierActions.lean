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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions

/-!
# Actual integrated actions of the original Haar-core multipliers

Integrating the original coefficient and group actions gives multiplication
by the covariant coefficient operators and group unitaries. Consequently each
covariant operator seminorm has the actual coefficient bound and is unchanged
by either group action. These are prerequisites for the canonical multiplier
maps on the full crossed product. No raw-core norm or completed-model datum is
assumed, and no all-covariant supremum identity is asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CompactlySupported CStarAlgebra

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- Original left coefficients integrate to left multiplication by the actual coefficient operator. -/
theorem haarIntegratedHom_coefficientLeft (a : A) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.coefficientLeft μ α a f) =
      ρ.algebra a * haarIntegratedHom μ ρ f := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  change (∫ s : G, ρ.algebra (a * f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ) =
    ρ.algebra a (haarIntegratedHom μ ρ f ξ)
  simp_rw [map_mul ρ.algebra]
  change (∫ s : G, ρ.algebra a (ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ)) ∂μ) =
    ρ.algebra a (∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ)
  exact (ρ.algebra a).integral_comp_comm
    (StronglyContinuousUnitaryRepresentation.integratedVector_integrable μ ρ.group ρ.algebra
      (HaarTwistedCore.toCc μ α f) ξ)

/-- Original right coefficients integrate to right multiplication by the actual coefficient operator. -/
theorem haarIntegratedHom_coefficientRight (a : A) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.coefficientRight μ α a f) =
      haarIntegratedHom μ ρ f * ρ.algebra a := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  change (∫ s : G, ρ.algebra (f s * α s a) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ) =
    haarIntegratedHom μ ρ f (ρ.algebra a ξ)
  rw [haarIntegratedHom_apply_vector]
  apply integral_congr_ae
  filter_upwards [] with s
  have hu : star (ρ.group s : H →L[ℂ] H) * (ρ.group s : H →L[ℂ] H) = 1 :=
    (ρ.group s).prop.1
  have hCov : ρ.algebra (α s a) * (ρ.group s : H →L[ℂ] H) =
      (ρ.group s : H →L[ℂ] H) * ρ.algebra a := by
    rw [← ρ.covariance s a]
    simp only [mul_assoc, hu, mul_one]
  have hOp : ρ.algebra (f s * α s a) * (ρ.group s : H →L[ℂ] H) =
      ρ.algebra (f s) * (ρ.group s : H →L[ℂ] H) * ρ.algebra a := by
    rw [map_mul ρ.algebra]
    simpa only [mul_assoc] using congrArg (fun T => ρ.algebra (f s) * T) hCov
  exact congrArg (fun T : H →L[ℂ] H => T ξ) hOp

/-- Original inverse left translation integrates to left multiplication by the group unitary. -/
theorem haarIntegratedHom_groupLeft (g : G) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.groupLeft μ α g f) =
      (ρ.group g : H →L[ℂ] H) * haarIntegratedHom μ ρ f := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  let K : G → H := fun s =>
    ρ.algebra (α g (f (g⁻¹ * s))) ((ρ.group s : H →L[ℂ] H) ξ)
  change (∫ s : G, K s ∂μ) = (ρ.group g : H →L[ℂ] H) (haarIntegratedHom μ ρ f ξ)
  calc
    _ = ∫ t : G, K (g * t) ∂μ := (integral_mul_left_eq_self (μ := μ) K g).symm
    _ = ∫ t : G, (ρ.group g : H →L[ℂ] H)
        (ρ.algebra (f t) ((ρ.group t : H →L[ℂ] H) ξ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hu : star (ρ.group g : H →L[ℂ] H) * (ρ.group g : H →L[ℂ] H) = 1 :=
        (ρ.group g).prop.1
      have hCov : ρ.algebra (α g (f t)) * (ρ.group g : H →L[ℂ] H) =
          (ρ.group g : H →L[ℂ] H) * ρ.algebra (f t) := by
        rw [← ρ.covariance g (f t)]
        simp only [mul_assoc, hu, mul_one]
      simp only [K, inv_mul_cancel_left, ρ.group.apply_mul]
      exact congrArg (fun T : H →L[ℂ] H => T ((ρ.group t : H →L[ℂ] H) ξ)) hCov
    _ = (ρ.group g : H →L[ℂ] H)
        (∫ t : G, ρ.algebra (f t) ((ρ.group t : H →L[ℂ] H) ξ) ∂μ) :=
      (ρ.group g : H →L[ℂ] H).integral_comp_comm
        (StronglyContinuousUnitaryRepresentation.integratedVector_integrable μ ρ.group ρ.algebra
          (HaarTwistedCore.toCc μ α f) ξ)
    _ = _ := rfl

/-- Original modular right translation integrates to right multiplication by the group unitary. -/
theorem haarIntegratedHom_groupRight (g : G) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.groupRight μ α g f) =
      haarIntegratedHom μ ρ f * (ρ.group g : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  let F : G → H := fun s =>
    ρ.algebra (f (s * g⁻¹)) ((ρ.group s : H →L[ℂ] H) ξ)
  change (∫ s : G, ρ.algebra (((Measure.modularCharacter g : ℝ) : ℂ) • f (s * g⁻¹))
    ((ρ.group s : H →L[ℂ] H) ξ) ∂μ) =
      haarIntegratedHom μ ρ f ((ρ.group g : H →L[ℂ] H) ξ)
  calc
    _ = ∫ s : G, (Measure.modularCharacter g : ℝ) • F s ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [map_smul]
      rfl
    _ = (Measure.modularCharacter g : ℝ) • ∫ s : G, F s ∂μ := integral_smul _ _
    _ = ∫ t : G, F (t * g) ∂μ := (integral_mul_right_modular μ F g).symm
    _ = ∫ t : G, ρ.algebra (f t)
        ((ρ.group t : H →L[ℂ] H) ((ρ.group g : H →L[ℂ] H) ξ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [F, mul_inv_cancel_right, ρ.group.apply_mul]
    _ = _ := rfl

/-- Every covariant seminorm has the actual left coefficient norm bound. -/
theorem norm_haarIntegratedHom_coefficientLeft_le (a : A) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.coefficientLeft μ α a f)‖ ≤
      ‖a‖ * ‖haarIntegratedHom μ ρ f‖ := by
  rw [haarIntegratedHom_coefficientLeft]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ρ.algebra a) (norm_nonneg _))

/-- Every covariant seminorm has the actual right coefficient norm bound. -/
theorem norm_haarIntegratedHom_coefficientRight_le (a : A) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.coefficientRight μ α a f)‖ ≤
      ‖haarIntegratedHom μ ρ f‖ * ‖a‖ := by
  rw [haarIntegratedHom_coefficientRight]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le ρ.algebra a) (norm_nonneg _))

/-- Every covariant seminorm is unchanged by original inverse left translation. -/
theorem norm_haarIntegratedHom_groupLeft (g : G) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.groupLeft μ α g f)‖ =
      ‖haarIntegratedHom μ ρ f‖ := by
  rw [haarIntegratedHom_groupLeft]
  exact CStarRing.norm_coe_unitary_mul (ρ.group g) (haarIntegratedHom μ ρ f)

/-- Every covariant seminorm is unchanged by original modular right translation. -/
theorem norm_haarIntegratedHom_groupRight (g : G) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.groupRight μ α g f)‖ =
      ‖haarIntegratedHom μ ρ f‖ := by
  rw [haarIntegratedHom_groupRight]
  exact CStarRing.norm_mul_coe_unitary (haarIntegratedHom μ ρ f) (ρ.group g)

end

end CovariantRepresentation
