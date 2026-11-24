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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.CovariantRepresentation
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Vector-integrated operators of strong unitary representations

For a coefficient star homomorphism and a strongly continuous unitary
representation, integration on each Hilbert vector defines a bounded
operator. Compact support supplies integrability, and the operator norm is
bounded by the integral of the coefficient norm. Covariance is not needed
for this construction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CStarAlgebra

namespace StronglyContinuousUnitaryRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : StronglyContinuousUnitaryRepresentation G H)
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Each compact coefficient function has an integrable original Hilbert-vector action. -/
theorem integratedVector_integrable
    (f : CompactlySupportedContinuousMap G A) (ξ : H) :
    Integrable (fun g : G => π (f g) ((U g : H →L[ℂ] H) ξ)) μ := by
  have hcont : Continuous (fun g : G => π (f g) ((U g : H →L[ℂ] H) ξ)) :=
    ((map_continuous π).comp f.continuous).clm_apply (U.continuous_orbit ξ)
  have hsupport : HasCompactSupport
      (fun g : G => π (f g) ((U g : H →L[ℂ] H) ξ)) := by
    apply hasCompactSupport_iff_eventuallyEq.mpr
    have hf := hasCompactSupport_iff_eventuallyEq.mp f.hasCompactSupport
    filter_upwards [hf] with g hg
    change π (f g) ((U g : H →L[ℂ] H) ξ) = 0
    have hzero : f g = (0 : A) := hg
    rw [hzero, map_zero]
    rfl
  exact hcont.integrable_of_hasCompactSupport hsupport

/-- The actual vector integral has the compact coefficient L1 bound. -/
theorem norm_integratedVector_le
    (f : CompactlySupportedContinuousMap G A) (ξ : H) :
    ‖∫ g : G, π (f g) ((U g : H →L[ℂ] H) ξ) ∂μ‖ ≤
      (∫ g : G, ‖f g‖ ∂μ) * ‖ξ‖ := by
  have hnorm : Integrable (fun g : G => ‖f g‖ * ‖ξ‖) μ :=
    (f.continuous.norm.integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_left (g := fun a : A => ‖a‖) norm_zero)).mul_const _
  have hbound (g : G) : ‖π (f g) ((U g : H →L[ℂ] H) ξ)‖ ≤ ‖f g‖ * ‖ξ‖ := by
    calc
      _ ≤ ‖π (f g)‖ * ‖(U g : H →L[ℂ] H) ξ‖ := (π (f g)).le_opNorm _
      _ ≤ ‖f g‖ * ‖(U g : H →L[ℂ] H) ξ‖ :=
        mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π (f g)) (norm_nonneg _)
      _ = ‖f g‖ * ‖ξ‖ := by rw [U.norm_apply g ξ]
  calc
    _ ≤ ∫ g : G, ‖f g‖ * ‖ξ‖ ∂μ :=
      norm_integral_le_of_norm_le hnorm (Eventually.of_forall hbound)
    _ = (∫ g : G, ‖f g‖ ∂μ) * ‖ξ‖ := integral_mul_const _ _

/-- The actual operator obtained by Bochner integration on every Hilbert vector. -/
def integratedOperator (f : CompactlySupportedContinuousMap G A) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun ξ => ∫ g : G, π (f g) ((U g : H →L[ℂ] H) ξ) ∂μ
      map_add' := fun ξ η => by
        simp_rw [map_add]
        exact integral_add
          (integratedVector_integrable μ U π f ξ) (integratedVector_integrable μ U π f η)
      map_smul' := fun c ξ => by
        simp_rw [map_smul]
        exact integral_smul c _ }
    (∫ g : G, ‖f g‖ ∂μ) (norm_integratedVector_le μ U π f)

/-- The complete vector action of the constructed operator. -/
@[simp]
theorem integratedOperator_apply (f : CompactlySupportedContinuousMap G A) (ξ : H) :
    integratedOperator μ U π f ξ = ∫ g : G, π (f g) ((U g : H →L[ℂ] H) ξ) ∂μ :=
  rfl

/-- The operator norm has the original compact coefficient's `L¹` bound. -/
theorem norm_integratedOperator_le (f : CompactlySupportedContinuousMap G A) :
    ‖integratedOperator μ U π f‖ ≤ ∫ g : G, ‖f g‖ ∂μ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun g => norm_nonneg (f g))
  intro ξ
  exact norm_integratedVector_le μ U π f ξ

/-- Coefficient addition gives the actual sum of integrated operators. -/
@[simp]
theorem integratedOperator_add (f k : CompactlySupportedContinuousMap G A) :
    integratedOperator μ U π (f + k) = integratedOperator μ U π f + integratedOperator μ U π k := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [integratedOperator_apply, CompactlySupportedContinuousMap.add_apply,
    map_add, add_apply]
  exact integral_add
    (integratedVector_integrable μ U π f ξ) (integratedVector_integrable μ U π k ξ)

/-- Complex coefficient scaling gives the actual scaled integrated operator. -/
@[simp]
theorem integratedOperator_smul (c : ℂ) (f : CompactlySupportedContinuousMap G A) :
    integratedOperator μ U π (c • f) = c • integratedOperator μ U π f := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [integratedOperator_apply, CompactlySupportedContinuousMap.smul_apply,
    map_smul, smul_apply]
  exact integral_smul c _

end

end StronglyContinuousUnitaryRepresentation
