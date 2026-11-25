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
# Isometric coefficient embedding in the full crossed product

Let G be a locally compact topological group with regular left Haar measure μ, and α a
point-norm action on a nonunital complex C-star algebra A. Complete the compactly supported
twisted-convolution algebra for its maximal covariant C-star seminorm. The coefficient
homomorphism j:A→𝓜(FullCovariantCompletion μ α) is injective and satisfies ‖j(a)‖=‖a‖. On the
dense core, j(a) acts by left multiplication: j(a)ι(f)=ι(s↦a*f(s)). These statements include
the zero coefficient algebra.
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

/-- **C-star algebra of bounded Hilbert-space operators.**

For a complete complex inner-product space H, the bounded complex linear operators H→L[ℂ]H
form a unital C-star algebra under composition, the operator norm and the Hilbert adjoint.
-/
local instance : CStarAlgebra (H →L[ℂ] H) := inferInstance

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- **Vanishing integrated coefficient action annihilates products.**

Let ρ be a covariant representation of α on a complex Hilbert space H, and a∈A. If Iρ(a⋅f)=0
for every compactly supported twisted-convolution coefficient f, then ρ.algebra(a*b)=0 for
every b∈A; here (a⋅f)(s)=a*f(s).
-/
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

/-- **Vanishing integrated coefficient action annihilates the coefficient.**

Let ρ be a covariant representation and a∈A. If Iρ(a⋅f)=0 for every compactly supported
coefficient f, where (a⋅f)(s)=a*f(s), then ρ.algebra(a)=0.
-/
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

/-- **Coefficient homomorphism into the full multiplier algebra.**

For a point-norm action α of G on A and regular Haar measure μ, the coefficient homomorphism
j:A→𝓜(FullCovariantCompletion μ α) acts on dense compactly supported coefficients by
j(a)ι(f)=ι(s↦a*f(s)).
-/
def fullCoefficientMultiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, FullCovariantCompletion μ α) :=
  coefficientMultiplierHom μ α (maximalCStarSeminorm μ α)

omit [μ.Regular] in
/-- **Coefficient homomorphism for the maximal covariant seminorm.**

For a∈A, `fullCoefficientMultiplierHom μ α a = coefficientMultiplierHom μ α
(maximalCStarSeminorm μ α) a`. Thus the full coefficient multiplier is the coefficient action
on the maximal-seminorm completion.
-/
@[simp]
theorem fullCoefficientMultiplierHom_apply (a : A) :
    fullCoefficientMultiplierHom μ α a =
      coefficientMultiplierHom μ α (maximalCStarSeminorm μ α) a := rfl

/-- **A zero full coefficient multiplier has zero coefficient.**

For a∈A, if `coefficientMultiplierHom μ α (maximalCStarSeminorm μ α) a = 0`, then a=0.
-/
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

/-- **Injectivity of the full coefficient homomorphism.**

The coefficient homomorphism `fullCoefficientMultiplierHom μ α : A → 𝓜(FullCovariantCompletion
μ α)` is injective for every nonunital C-star algebra A and point-norm action α under the
stated Haar hypotheses.
-/
theorem fullCoefficientMultiplierHom_injective :
    Function.Injective (fullCoefficientMultiplierHom μ α) := by
  change Function.Injective (coefficientMultiplierHom μ α (maximalCStarSeminorm μ α))
  intro a b hab
  apply sub_eq_zero.mp
  apply fullCoefficientMultiplier_eq_zero_implies μ α (a - b)
  rw [map_sub, hab, sub_self]

/-- **Norm of a full coefficient multiplier.**

For a∈A, the full coefficient multiplier has exactly the C-star norm of a:
`‖fullCoefficientMultiplierHom μ α a‖ = ‖a‖`.
-/
theorem norm_fullCoefficientMultiplierHom (a : A) :
    ‖fullCoefficientMultiplierHom μ α a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (fullCoefficientMultiplierHom μ α)
    (fullCoefficientMultiplierHom_injective μ α) a

/-- **Isometric coefficient homomorphism.**

The coefficient homomorphism from A into the multiplier algebra of the full covariant
completion is an isometry: `‖fullCoefficientMultiplierHom μ α a‖ = ‖a‖` for every a∈A.
-/
theorem fullCoefficientMultiplierHom_isometry : Isometry (fullCoefficientMultiplierHom μ α) :=
  NonUnitalStarAlgHom.isometry (fullCoefficientMultiplierHom μ α)
    (fullCoefficientMultiplierHom_injective μ α)

/-- **Coefficient algebra embedded in full multipliers.**

The injective coefficient star homomorphism gives the function embedding
A↪𝓜(FullCovariantCompletion μ α), a↦fullCoefficientMultiplierHom μ α a.
-/
def fullCoefficientEmbedding : A ↪ 𝓜(ℂ, FullCovariantCompletion μ α) where
  toFun := fullCoefficientMultiplierHom μ α
  inj' := fullCoefficientMultiplierHom_injective μ α

/-- **Value of the full coefficient embedding.**

For a∈A, `fullCoefficientEmbedding μ α a = coefficientMultiplierHom μ α (maximalCStarSeminorm
μ α) a`.
-/
@[simp]
theorem fullCoefficientEmbedding_apply (a : A) :
    fullCoefficientEmbedding μ α a = coefficientMultiplierHom μ α (maximalCStarSeminorm μ α) a := rfl

/-- **Norm preservation by the coefficient embedding.**

For every a∈A, `‖fullCoefficientEmbedding μ α a‖ = ‖a‖` in the multiplier C-star norm.
-/
theorem norm_fullCoefficientEmbedding (a : A) : ‖fullCoefficientEmbedding μ α a‖ = ‖a‖ :=
  norm_fullCoefficientMultiplierHom μ α a

/-- **Left coefficient action on the dense full crossed-product core.**

For a∈A and a compactly supported coefficient f, `(fullCoefficientEmbedding μ α a).fst
(toFullCovariantCompletion μ α f) = toFullCovariantCompletion μ α (coefficientLeft μ α a f)`,
where (coefficientLeft a f)(s)=a*f(s).
-/
theorem fullCoefficientEmbedding_fst_apply (a : A) (f : Carrier μ α) :
    (fullCoefficientEmbedding μ α a).fst (toFullCovariantCompletion μ α f) =
      toFullCovariantCompletion μ α (coefficientLeft μ α a f) :=
  coefficientMultiplier_fst_apply μ α (maximalCStarSeminorm μ α) a f

end HaarTwistedCore

end
