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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedCoefficientMultiplier
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedGroupMultiplier
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.ConvolutionSeminormIntegral

/-!
# The actual algebraic coefficient/group multiplier pair

The coefficient and group maps are the computed same-seminorm multipliers.
Their original covariance is proved on the dense core and extended by
continuous equality. These literal maps form a pair with the covariance
proof as actual DATA. The full source pair's strict continuity and
nondegeneracy requirements remain separate.

For an admissible seminorm, the actual paired multiplier slices are
integrable on each original core vector and their Haar integral is its
original convolution image. This uses the constructed L1-to-seminorm
primitive, without a supplied integrated identity or full-norm comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped MultiplierAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- The computed completed multiplier maps retain the original covariance orientation. -/
theorem groupMultiplier_coefficientMultiplier (g : G) (a : A) :
    groupMultiplier μ α p g * coefficientMultiplier μ α p a =
      coefficientMultiplier μ α p (α g a) * groupMultiplier μ α p g := by
  apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
  · change groupLeftCompletion μ α p g (coefficientLeftCompletion μ α p a x) =
      coefficientLeftCompletion μ α p (α g a) (groupLeftCompletion μ α p g x)
    refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
      ((groupLeftCompletion μ α p g).continuous.comp
        (coefficientLeftCompletion μ α p a).continuous)
      ((coefficientLeftCompletion μ α p (α g a)).continuous.comp
        (groupLeftCompletion μ α p g).continuous) ?_) x
    funext f
    simp only [Function.comp_apply, coefficientLeftCompletion_apply, groupLeftCompletion_apply]
    simpa only [LinearMap.comp_apply] using
      congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => p.toNonUnitalCompletion (T f))
        (groupLeft_coefficientLeft μ α g a)
  · change coefficientRightCompletion μ α p a (groupRightCompletion μ α p g x) =
      groupRightCompletion μ α p g (coefficientRightCompletion μ α p (α g a) x)
    refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
      ((coefficientRightCompletion μ α p a).continuous.comp
        (groupRightCompletion μ α p g).continuous)
      ((groupRightCompletion μ α p g).continuous.comp
        (coefficientRightCompletion μ α p (α g a)).continuous) ?_) x
    funext f
    simp only [Function.comp_apply, coefficientRightCompletion_apply, groupRightCompletion_apply]
    simpa only [LinearMap.comp_apply] using
      congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => p.toNonUnitalCompletion (T f))
        (coefficientRight_groupRight μ α g a)

/-- The actual group multiplier conjugates the original completed coefficient by its given action. -/
theorem groupMultiplier_conjugates_coefficient (g : G) (a : A) :
    groupMultiplier μ α p g * coefficientMultiplier μ α p a * star (groupMultiplier μ α p g) =
      coefficientMultiplier μ α p (α g a) := by
  rw [groupMultiplier_coefficientMultiplier, mul_assoc,
    Unitary.mul_star_self_of_mem (groupMultiplier_mem_unitary μ α p g), mul_one]

/-- The literal computed multiplier maps together with their proved algebraic covariance DATA. -/
def canonicalMultiplierPair :
    { pair : (A →⋆ₙₐ[ℂ] 𝓜(ℂ, p.NonUnitalCompletion)) ×
        (G →* unitary 𝓜(ℂ, p.NonUnitalCompletion)) //
      ∀ g : G, ∀ a : A,
        (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) * pair.1 a *
          star (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) = pair.1 (α g a) } :=
  ⟨⟨coefficientMultiplierHom μ α p, groupUnitaryMultiplierHom μ α p⟩, fun g a => by
    change groupMultiplier μ α p g * coefficientMultiplier μ α p a *
      star (groupMultiplier μ α p g) = coefficientMultiplier μ α p (α g a)
    exact groupMultiplier_conjugates_coefficient μ α p g a⟩

/-- The pair retains exactly the actual computed coefficient homomorphism. -/
@[simp]
theorem canonicalMultiplierPair_coefficient :
    (canonicalMultiplierPair μ α p).val.1 = coefficientMultiplierHom μ α p := rfl

/-- The pair retains exactly the actual computed unitary group homomorphism. -/
@[simp]
theorem canonicalMultiplierPair_group :
    (canonicalMultiplierPair μ α p).val.2 = groupUnitaryMultiplierHom μ α p := rfl

/-- The literal pair has the original conjugation equation without a supplied covariance witness. -/
theorem canonicalMultiplierPair_covariance (g : G) (a : A) :
    ((canonicalMultiplierPair μ α p).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) *
        (canonicalMultiplierPair μ α p).val.1 a *
          star ((canonicalMultiplierPair μ α p).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) =
      (canonicalMultiplierPair μ α p).val.1 (α g a) :=
  (canonicalMultiplierPair μ α p).property g a

/-- Each paired multiplier slice has exactly its original coefficient/group value on the dense core. -/
theorem canonicalMultiplierPair_slice_apply (f : Carrier μ α) (s : G) (h : Carrier μ α) :
    ((canonicalMultiplierPair μ α p).val.1 (f s) *
        ((canonicalMultiplierPair μ α p).val.2 s : 𝓜(ℂ, p.NonUnitalCompletion))).fst
          (p.toNonUnitalCompletion h) =
      p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
  change coefficientLeftCompletion μ α p (f s)
    (groupLeftCompletion μ α p s (p.toNonUnitalCompletion h)) = _
  rw [groupLeftCompletion_apply, coefficientLeftCompletion_apply]

variable (hp : p ∈ admissibleCStarSeminorms μ α)

include hp in
/-- Actual paired multiplier slices are integrable at every original source-core vector. -/
theorem integrable_canonicalMultiplierPair_slice (f h : Carrier μ α) :
    let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
    Integrable (fun s : G =>
      ((canonicalMultiplierPair μ α p).val.1 (f s) *
          ((canonicalMultiplierPair μ α p).val.2 s : 𝓜(ℂ, p.NonUnitalCompletion))).fst
            (p.toNonUnitalCompletion h)) μ := by
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  apply (integrable_toNonUnitalCompletion_coefficientLeft_groupLeft μ α p hp f h).congr
  exact Eventually.of_forall fun s => (canonicalMultiplierPair_slice_apply μ α p f s h).symm

include hp in
/-- The actual paired multiplier integral on the dense core is the original convolution image. -/
theorem integral_canonicalMultiplierPair_slice (f h : Carrier μ α) :
    let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
    (∫ s : G,
      ((canonicalMultiplierPair μ α p).val.1 (f s) *
          ((canonicalMultiplierPair μ α p).val.2 s : 𝓜(ℂ, p.NonUnitalCompletion))).fst
            (p.toNonUnitalCompletion h) ∂μ) = p.toNonUnitalCompletion (f * h) := by
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  calc
    _ = ∫ s : G, p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun s => canonicalMultiplierPair_slice_apply μ α p f s h)
    _ = _ := integral_toNonUnitalCompletion_coefficientLeft_groupLeft μ α p hp f h

end

end HaarTwistedCore
