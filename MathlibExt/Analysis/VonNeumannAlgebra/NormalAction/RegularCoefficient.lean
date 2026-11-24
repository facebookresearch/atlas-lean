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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.Continuity
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.PointwiseOperator
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularRepresentation
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The actual regular coefficient operator of a normal action

The original compact-support formula is alpha(s inverse)(x) applied to the
original vector at s. The existing normal-action vector continuity and
automorphism norm bound supply the shared bounded pointwise L2 construction.
These original regular-coefficient names are wrappers around that construction
on the actual source seminorm, its separation quotient and ordinary completion,
and the original Lp H 2 Haar carrier.

The shared operator retains the literal formula almost everywhere on every
Lp vector. The source action is normal with continuous predual orbits, rather
than a different norm-continuous C-star action. Connes's tensor transport is
separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2 Filter
open scoped ENNReal Topology CompactlySupported InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra
namespace NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The inverse-coordinate coefficient field has jointly continuous vector action. -/
theorem continuous_regularCoefficientField (α : NormalAction G M) (x : M) :
    Continuous fun p : G × H => (α p.1⁻¹ x : H →L[ℂ] H) p.2 :=
  (continuous_vector_action α x).comp
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The original algebra norm bounds every inverse-coordinate coefficient operator. -/
theorem regularCoefficientField_norm_le (α : NormalAction G M) (x : M) (s : G) :
    ‖(α s⁻¹ x : H →L[ℂ] H)‖ ≤ ‖x‖ := by
  change ‖α s⁻¹ x‖ ≤ ‖x‖
  exact (StarAlgEquiv.norm_map (α s⁻¹).toStarAlgEquiv x).le

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The original regular coefficient action on continuous compact-support vectors. -/
def regularCoefficientCompactSupport (α : NormalAction G M) (x : M) :
    C_c(G, H) →ₗ[ℂ] C_c(G, H) :=
  pointwiseCompactSupport (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x)

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The compact-support action keeps the original inverse group-coordinate formula. -/
@[simp]
theorem regularCoefficientCompactSupport_apply (α : NormalAction G M) (x : M)
    (f : C_c(G, H)) (s : G) :
    regularCoefficientCompactSupport α x f s = (α s⁻¹ x : H →L[ℂ] H) (f s) :=
  rfl

variable (μ : Measure G) [μ.Regular]

omit [LocallyCompactSpace G] in
/-- The original operator norm bounds the actual compact-support L2 images. -/
theorem regularCoefficientCompactSupport_l2Bound (α : NormalAction G M) (x : M)
    (f : C_c(G, H)) :
    ‖compactSupportInclusion μ (regularCoefficientCompactSupport α x f)‖ ≤
      ‖x‖ * ‖compactSupportInclusion μ f‖ :=
  pointwiseCompactSupport_l2Bound (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) f

omit [LocallyCompactSpace G] in
/-- The bounded compact-support coefficient map descends and extends through the genuine source completion. -/
def regularCoefficientSourceMap (α : NormalAction G M) (x : M) :
    CompletionCore (H := H) μ →L[ℂ] Lp H 2 μ :=
  pointwiseSourceMap (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x)

omit [LocallyCompactSpace G] in
/-- The extended source map retains each original compact-support coefficient image. -/
theorem regularCoefficientSourceMap_apply (α : NormalAction G M) (x : M) (f : C_c(G, H)) :
    regularCoefficientSourceMap μ α x (toCompletion μ f) =
      compactSupportInclusion μ (regularCoefficientCompactSupport α x f) :=
  pointwiseSourceMap_apply (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) f

/-- The actual regular coefficient operator on the same original Haar Lp H 2 carrier. -/
def regularCoefficient (α : NormalAction G M) (x : M) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  pointwiseOperator (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x)

/-- The actual Lp operator retains the exact compact-support inverse-action formula. -/
theorem regularCoefficient_apply_compactSupport (α : NormalAction G M) (x : M)
    (f : C_c(G, H)) :
    regularCoefficient μ α x (compactSupportInclusion μ f) =
      compactSupportInclusion μ (regularCoefficientCompactSupport α x f) :=
  pointwiseOperator_apply_compactSupport (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) f

/-- Every actual Lp vector has the literal original regular coefficient representative almost everywhere. -/
theorem regularCoefficient_ae_eq (α : NormalAction G M) (x : M) (ξ : Lp H 2 μ) :
    regularCoefficient μ α x ξ =ᵐ[μ] fun s : G => (α s⁻¹ x : H →L[ℂ] H) (ξ s) :=
  pointwiseOperator_ae_eq (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) ξ

/-- The actual original algebra norm bounds every Haar L2 vector image. -/
theorem regularCoefficient_norm_apply_le (α : NormalAction G M) (x : M) (ξ : Lp H 2 μ) :
    ‖regularCoefficient μ α x ξ‖ ≤ ‖x‖ * ‖ξ‖ :=
  pointwiseOperator_norm_apply_le (fun s => (α s⁻¹ x : H →L[ℂ] H))
    (continuous_regularCoefficientField α x) μ ‖x‖ (regularCoefficientField_norm_le α x) ξ

/-- The same actual coefficient operator on the original separated C_c completion. -/
def regularCoefficientOriginal (α : NormalAction G M) (x : M) :
    CompletionCore (H := H) μ →L[ℂ] CompletionCore (H := H) μ :=
  (completionToLp (H := H) μ).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((regularCoefficient μ α x).comp
      (completionToLp (H := H) μ).toLinearIsometry.toContinuousLinearMap)

/-- The original source-completion operator has the original compact-support coordinate formula. -/
theorem regularCoefficientOriginal_apply (α : NormalAction G M) (x : M) (f : C_c(G, H)) :
    regularCoefficientOriginal μ α x (toCompletion μ f) =
      toCompletion μ (regularCoefficientCompactSupport α x f) := by
  change (completionToLp (H := H) μ).symm
      (regularCoefficient μ α x ((completionToLp (H := H) μ) (toCompletion μ f))) = _
  rw [completionToLp_apply, regularCoefficient_apply_compactSupport,
    ← completionToLp_apply μ (regularCoefficientCompactSupport α x f),
    LinearIsometryEquiv.symm_apply_apply]

end

end NormalAction
end VonNeumannAlgebra
