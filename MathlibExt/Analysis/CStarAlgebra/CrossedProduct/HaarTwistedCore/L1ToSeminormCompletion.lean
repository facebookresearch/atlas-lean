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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Completion
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MaximalSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Hom

/-!
# The original Haar L1 completion maps to every admissible seminorm completion

The canonical map for the actual seminorm is bounded by the literal L1
coefficient integral. Extend that same nonunital star-algebra map through
the existing completion factory. Its canonical coefficient values and
contractive complex linear map supply the integral transport used to build
the original covariant representation of an admissible seminorm.

The seminorm and coefficient algebra may be zero. No covariant norm
comparison or integrated identity is an input to these constructed data.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)
variable (p : CStarSeminorm (Carrier μ α)) (hp : p ∈ admissibleCStarSeminorms μ α)

/-- The original canonical seminorm map is bounded in the actual source L1 norm. -/
def sourceToSeminormCompletionCLM :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Carrier μ α →L[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let L : Carrier μ α →ₗ[ℂ] p.NonUnitalCompletion :=
    { toFun := p.toNonUnitalCompletion
      map_add' := map_add p.toNonUnitalCompletion
      map_smul' := fun c f => map_smul p.toNonUnitalCompletion c f }
  exact L.mkContinuous 1 (by
    intro f
    change ‖p.toNonUnitalCompletion f‖ ≤ 1 * l1Gauge μ α f
    rw [p.norm_toNonUnitalCompletion, one_mul]
    exact hp f)

omit [μ.Regular] in
/-- The bounded raw map retains the original quotient-and-completion value. -/
theorem sourceToSeminormCompletionCLM_apply (f : Carrier μ α) :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    sourceToSeminormCompletionCLM μ α p hp f = p.toNonUnitalCompletion f :=
  rfl

/-- Extend the same canonical star map to the actual ordinary L1 completion. -/
def l1ToSeminormCompletion :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    L1Completion μ α →⋆ₙₐ[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact NonUnitalStarAlgHom.fromCompletion p.toNonUnitalCompletion
    (sourceToSeminormCompletionCLM μ α p hp).continuous

/-- Every original coefficient has the same actual seminorm-completion image. -/
theorem l1ToSeminormCompletion_apply (f : Carrier μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    l1ToSeminormCompletion μ α p hp (toL1Completion μ α f) = p.toNonUnitalCompletion f := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact NonUnitalStarAlgHom.fromCompletion_apply_coe p.toNonUnitalCompletion
    (sourceToSeminormCompletionCLM μ α p hp).continuous f

/-- The same star map is continuous in the original L1 completion topology. -/
theorem continuous_l1ToSeminormCompletion :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Continuous (l1ToSeminormCompletion μ α p hp) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact NonUnitalStarAlgHom.continuous_fromCompletion p.toNonUnitalCompletion
    (sourceToSeminormCompletionCLM μ α p hp).continuous

/-- The original L1 bound extends to every element of the same completion. -/
theorem norm_l1ToSeminormCompletion_le (x : L1Completion μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    ‖l1ToSeminormCompletion μ α p hp x‖ ≤ ‖x‖ := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  have hcont := continuous_l1ToSeminormCompletion μ α p hp
  refine (denseRange_toL1Completion μ α).induction_on x
    (isClosed_le hcont.norm continuous_norm) ?_
  intro f
  change ‖l1ToSeminormCompletion μ α p hp (toL1Completion μ α f)‖ ≤
    ‖toL1Completion μ α f‖
  rw [l1ToSeminormCompletion_apply, p.norm_toNonUnitalCompletion]
  change p f ≤ ‖toL1Completion μ α f‖
  rw [norm_toL1Completion]
  exact hp f

/-- The same actual comparison function as a contractive complex linear map. -/
def l1ToSeminormCompletionCLM :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    L1Completion μ α →L[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let L : L1Completion μ α →ₗ[ℂ] p.NonUnitalCompletion :=
    { toFun := l1ToSeminormCompletion μ α p hp
      map_add' := map_add (l1ToSeminormCompletion μ α p hp)
      map_smul' := fun c x => map_smul (l1ToSeminormCompletion μ α p hp) c x }
  exact L.mkContinuous 1 (by
    intro x
    change ‖l1ToSeminormCompletion μ α p hp x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_l1ToSeminormCompletion_le μ α p hp x)

/-- The comparison's linear and star-algebra views have the same values. -/
theorem l1ToSeminormCompletionCLM_apply (x : L1Completion μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    l1ToSeminormCompletionCLM μ α p hp x = l1ToSeminormCompletion μ α p hp x :=
  rfl

end

end HaarTwistedCore
