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

public import MathlibExt.MeasureTheory.Integral.CompactScalarSeparation
public import MathlibExt.Analysis.CStarAlgebra.CanonicalApproximateUnit
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedMultiplierActions
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.CanonicalHaarRegularModel
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarRegularCoefficientFaithful
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedCoefficientMultiplier
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FullCovariantSeminorm
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The actual original full coefficient multiplier embedding

Compact scalar Haar tests recover the original coefficient products from a
zero integrated left action. The computed coefficient approximate unit
then recovers the original coefficient. Apply this to the internally
constructed canonical regular pair and its verified faithful coefficient
map: no faithful representation, norm or multiplier model is an input.

The actual full coefficient homomorphism is therefore injective, and the
existing C-star homomorphism theorem gives its original coefficient norm.
This does not assert a group embedding in the zero-coefficient case or
use regular integrated nondegeneracy, quotient surjectivity or a supplied
convolution approximate identity.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CompactlySupported MultiplierAlgebra CStarAlgebra Topology

noncomputable section

namespace CovariantRepresentation

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual bounded operators on the original complete Hilbert space have their stock C-star data. -/
local instance : CStarAlgebra (H →L[ℂ] H) := inferInstance

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- Original compact Haar tests recover each coefficient product from its zero integrated left action. -/
theorem algebra_mul_eq_zero_of_integratedCoefficientLeft_eq_zero (a : A)
    (hZero : ∀ f : HaarTwistedCore.Carrier μ α,
      haarIntegratedHom μ ρ (HaarTwistedCore.coefficientLeft μ α a f) = 0) (b : A) :
    ρ.algebra (a * b) = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  let F : G → H := fun g => ρ.algebra (a * b) ((ρ.group g : H →L[ℂ] H) ξ)
  have hF : Continuous F := (ρ.algebra (a * b)).continuous.comp (ρ.group.continuous_orbit ξ)
  have hTest (ψ : C_c(G, ℂ)) : (∫ g : G, ψ g • F g ∂μ) = 0 := by
    let fc : C_c(G, A) :=
      { toFun g := ψ g • b
        continuous_toFun := (map_continuous ψ).smul continuous_const
        hasCompactSupport' := ψ.hasCompactSupport.comp_left
          (g := fun z : ℂ => z • b) (zero_smul ℂ b) }
    let f := HaarTwistedCore.fromCc μ α fc
    have h := congrArg (fun T : H →L[ℂ] H => T ξ) (hZero f)
    rw [haarIntegratedHom_apply_vector] at h
    simp only [zero_apply] at h
    have hValue (g : G) :
        ρ.algebra (HaarTwistedCore.coefficientLeft μ α a f g) ((ρ.group g : H →L[ℂ] H) ξ) =
          ψ g • F g := by
      change ρ.algebra (a * (ψ g • b)) ((ρ.group g : H →L[ℂ] H) ξ) =
        ψ g • ρ.algebra (a * b) ((ρ.group g : H →L[ℂ] H) ξ)
      simp only [mul_smul_comm, map_smul, smul_apply]
    exact (integral_congr_ae (Eventually.of_forall fun g => (hValue g).symm)).trans h
  have h := hF.eq_zero_of_compactScalar_integrals_eq_zero μ (1 : G) hTest
  simpa only [F, ρ.group.apply_one, zero_apply] using h

/-- The actual coefficient approximate unit recovers a coefficient from all its zero integrated left actions. -/
theorem algebra_eq_zero_of_integratedCoefficientLeft_eq_zero (a : A)
    (hZero : ∀ f : HaarTwistedCore.Carrier μ α,
      haarIntegratedHom μ ρ (HaarTwistedCore.coefficientLeft μ α a f) = 0) : ρ.algebra a = 0 := by
  let _ : (CStarAlgebra.canonicalApproximateUnit A).NeBot := CStarAlgebra.canonicalApproximateUnit_neBot A
  have hProduct : Tendsto (fun b : A => a * b) (CStarAlgebra.canonicalApproximateUnit A) (𝓝 a) :=
    CStarAlgebra.tendsto_canonicalApproximateUnit_mul_left A a
  have hLimit := ((map_continuous ρ.algebra).tendsto a).comp hProduct
  have hAll : (fun b : A => ρ.algebra (a * b)) = fun _ : A => (0 : H →L[ℂ] H) := by
    funext b
    exact algebra_mul_eq_zero_of_integratedCoefficientLeft_eq_zero μ ρ a hZero b
  have hLimitZero : Tendsto (fun b : A => ρ.algebra (a * b))
      (CStarAlgebra.canonicalApproximateUnit A) (𝓝 (0 : H →L[ℂ] H)) := by
    rw [hAll]
    exact tendsto_const_nhds
  simp only [Function.comp_def] at hLimit
  exact tendsto_nhds_unique hLimit hLimitZero

end CovariantRepresentation

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

/-- The named actual coefficient star-algebra homomorphism into the full multiplier algebra. -/
def fullCoefficientMultiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, FullCovariantCompletion μ α) :=
  coefficientMultiplierHom μ α (maximalCStarSeminorm μ α)

omit [μ.Regular] in
/-- The named full coefficient homomorphism is its exact computed same-seminorm specialization. -/
@[simp]
theorem fullCoefficientMultiplierHom_apply (a : A) :
    fullCoefficientMultiplierHom μ α a =
      coefficientMultiplierHom μ α (maximalCStarSeminorm μ α) a := rfl

/-- A zero actual full coefficient multiplier has zero original coefficient. -/
theorem fullCoefficientMultiplier_eq_zero_implies (a : A)
    (hZero : coefficientMultiplierHom μ α (maximalCStarSeminorm μ α) a = 0) : a = 0 := by
  let ρ := PointNormCStarAction.canonicalRegularCovariantRepresentation μ α
  have hCore (f : Carrier μ α) :
      (maximalCStarSeminorm μ α).toNonUnitalCompletion (coefficientLeft μ α a f) = 0 := by
    have h := congrArg (fun T : 𝓜(ℂ, (maximalCStarSeminorm μ α).NonUnitalCompletion) =>
      T.fst ((maximalCStarSeminorm μ α).toNonUnitalCompletion f)) hZero
    simpa only [coefficientMultiplierHom_apply, coefficientMultiplier_fst_apply,
      DoubleCentralizer.zero_fst, zero_apply] using h
  have hRaw (f : Carrier μ α) :
      CovariantRepresentation.haarIntegratedHom μ ρ (coefficientLeft μ α a f) = 0 := by
    have hGauge : maximalCStarSeminorm μ α (coefficientLeft μ α a f) = 0 := by
      rw [← CStarSeminorm.norm_toNonUnitalCompletion, hCore f, norm_zero]
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    simpa only [hGauge] using
      CovariantRepresentation.norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ (coefficientLeft μ α a f)
  have hCoefficient := CovariantRepresentation.algebra_eq_zero_of_integratedCoefficientLeft_eq_zero
    μ ρ a hRaw
  have hInjective : Function.Injective ρ.algebra := by
    change Function.Injective
      (α.regularCoefficientHom (PointNormCStarAction.canonicalCoefficientRepresentation A) μ)
    exact PointNormCStarAction.regularCoefficientHom_injective α
      (PointNormCStarAction.canonicalCoefficientRepresentation A) μ
      (PointNormCStarAction.canonicalCoefficientRepresentation_injective A)
  exact hInjective (hCoefficient.trans (map_zero ρ.algebra).symm)

/-- The computed original full coefficient homomorphism is injective, without a supplied faithful model. -/
theorem fullCoefficientMultiplierHom_injective :
    Function.Injective (fullCoefficientMultiplierHom μ α) := by
  change Function.Injective (coefficientMultiplierHom μ α (maximalCStarSeminorm μ α))
  intro a b hab
  apply sub_eq_zero.mp
  apply fullCoefficientMultiplier_eq_zero_implies μ α (a - b)
  rw [map_sub, hab, sub_self]

/-- The actual full coefficient multiplier norm is the original coefficient C-star norm. -/
theorem norm_fullCoefficientMultiplierHom (a : A) :
    ‖fullCoefficientMultiplierHom μ α a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (fullCoefficientMultiplierHom μ α)
    (fullCoefficientMultiplierHom_injective μ α) a

/-- The named original full coefficient homomorphism is isometric for the original C-star norm. -/
theorem fullCoefficientMultiplierHom_isometry : Isometry (fullCoefficientMultiplierHom μ α) :=
  NonUnitalStarAlgHom.isometry (fullCoefficientMultiplierHom μ α)
    (fullCoefficientMultiplierHom_injective μ α)

/-- The secondary function embedding retains the actual named coefficient star-algebra homomorphism. -/
def fullCoefficientEmbedding : A ↪ 𝓜(ℂ, FullCovariantCompletion μ α) where
  toFun := fullCoefficientMultiplierHom μ α
  inj' := fullCoefficientMultiplierHom_injective μ α

/-- The embedding retains exactly the original computed full coefficient multiplier. -/
@[simp]
theorem fullCoefficientEmbedding_apply (a : A) :
    fullCoefficientEmbedding μ α a = coefficientMultiplierHom μ α (maximalCStarSeminorm μ α) a := rfl

/-- The original full coefficient embedding retains the source coefficient norm. -/
theorem norm_fullCoefficientEmbedding (a : A) : ‖fullCoefficientEmbedding μ α a‖ = ‖a‖ :=
  norm_fullCoefficientMultiplierHom μ α a

/-- Every embedded coefficient still acts on each original full core image by the original left formula. -/
theorem fullCoefficientEmbedding_fst_apply (a : A) (f : Carrier μ α) :
    (fullCoefficientEmbedding μ α a).fst (toFullCovariantCompletion μ α f) =
      toFullCovariantCompletion μ α (coefficientLeft μ α a f) :=
  coefficientMultiplier_fst_apply μ α (maximalCStarSeminorm μ α) a f

end HaarTwistedCore

end
