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
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Completion
public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Hom

/-!
# The actual Haar-integrated representation on the original L1 completion

The literal L1 coefficient bound makes the original integrated star-algebra
homomorphism continuous for the computed L1 source norm. The existing
nonunital star-hom completion extension then acts on the same ordinary L1
completion. Its dense coefficient values are the original vector integral;
it is continuous and contractive, and these values determine it uniquely.

No approximate identity, source nondegeneracy, full covariant norm
comparison or alternative completed model is assumed by this construction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- The original coefficient-integral bound makes the same integrated map L1-continuous. -/
theorem continuous_haarIntegratedHom_for_L1 :
    let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
      HaarTwistedCore.sourceL1SeminormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
      HaarTwistedCore.sourceL1NormedSpace μ α
    Continuous (haarIntegratedHom μ ρ) := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let L : HaarTwistedCore.Carrier μ α →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := haarIntegratedHom μ ρ
      map_add' := map_add (haarIntegratedHom μ ρ)
      map_smul' := fun c f => map_smul (haarIntegratedHom μ ρ) c f }
  let T : HaarTwistedCore.Carrier μ α →L[ℂ] (H →L[ℂ] H) :=
    L.mkContinuous 1 (by
      intro f
      change ‖haarIntegratedHom μ ρ f‖ ≤ 1 * HaarTwistedCore.l1Gauge μ α f
      simpa only [one_mul, HaarTwistedCore.l1Gauge] using norm_haarIntegratedHom_le μ ρ f)
  exact T.continuous

/-- Extend the original integrated map through the same ordinary L1 completion. -/
def haarL1IntegratedHom :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    HaarTwistedCore.L1Completion μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H) := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  exact NonUnitalStarAlgHom.fromCompletion (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ)

/-- The same completed map retains every original integrated coefficient value. -/
theorem haarL1IntegratedHom_apply (f : HaarTwistedCore.Carrier μ α) :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    haarL1IntegratedHom μ ρ (HaarTwistedCore.toL1Completion μ α f) =
      haarIntegratedHom μ ρ f := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  exact NonUnitalStarAlgHom.fromCompletion_apply_coe (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ) f

/-- Every dense coefficient acts by the literal original Haar vector integral. -/
theorem haarL1IntegratedHom_apply_vector (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    haarL1IntegratedHom μ ρ (HaarTwistedCore.toL1Completion μ α f) ξ =
      ∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ := by
  rw [haarL1IntegratedHom_apply, haarIntegratedHom_apply_vector]

/-- The existing extension is continuous in the actual L1 completion topology. -/
theorem continuous_haarL1IntegratedHom :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    Continuous (haarL1IntegratedHom μ ρ) := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  exact NonUnitalStarAlgHom.continuous_fromCompletion (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ)

/-- The original L1 bound persists on every element of the same completed algebra. -/
theorem norm_haarL1IntegratedHom_le (x : HaarTwistedCore.L1Completion μ α) :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    ‖haarL1IntegratedHom μ ρ x‖ ≤ ‖x‖ := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  have hcont := continuous_haarL1IntegratedHom μ ρ
  refine UniformSpace.Completion.induction_on
    (α := HaarTwistedCore.Carrier μ α)
    (p := fun x : HaarTwistedCore.L1Completion μ α => ‖haarL1IntegratedHom μ ρ x‖ ≤ ‖x‖)
    x (isClosed_le (continuous_norm.comp hcont) continuous_norm) ?_
  intro f
  have hvalue : haarL1IntegratedHom μ ρ (f : HaarTwistedCore.L1Completion μ α) =
      haarIntegratedHom μ ρ f :=
    haarL1IntegratedHom_apply μ ρ f
  rw [hvalue, UniformSpace.Completion.norm_coe]
  change ‖haarIntegratedHom μ ρ f‖ ≤ HaarTwistedCore.l1Gauge μ α f
  exact norm_haarIntegratedHom_le μ ρ f

/-- A continuous nonunital star hom with the same dense original values is this extension. -/
theorem haarL1IntegratedHom_unique :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    ∀ ψ : HaarTwistedCore.L1Completion μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H),
      Continuous ψ →
        (∀ f : HaarTwistedCore.Carrier μ α,
          ψ (HaarTwistedCore.toL1Completion μ α f) = haarIntegratedHom μ ρ f) →
        ψ = haarL1IntegratedHom μ ρ := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let completionRing : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let completionNormedSpace : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let completionStar : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  change ∀ hom : HaarTwistedCore.L1Completion μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H),
    Continuous hom →
      (∀ f : HaarTwistedCore.Carrier μ α,
        hom (HaarTwistedCore.toL1Completion μ α f) = haarIntegratedHom μ ρ f) →
      hom = haarL1IntegratedHom μ ρ
  intro hom hhom hcoeff
  exact NonUnitalStarAlgHom.fromCompletion_unique (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ) hom hhom hcoeff

end

end CovariantRepresentation
