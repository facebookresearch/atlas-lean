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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormGroupActions
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Finite Gram invariance of the actual Haar-core group action

Use an actual Hilbert representation of the same-seminorm completion. The
source left group translation preserves each pairwise Gram product because
its original mixed star-convolution product is unchanged. Finite weighted
sums consequently preserve their inner products and inherited Hilbert norm.

This gives the kernel invariance needed to descend the group action to the
actual dense source Gram domain. No isometry, kernel, faithful model, source
normed ring or C-star ring conclusion is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace HaarTwistedCore

noncomputable section

universe uG uA uH uI uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Actual completed operator values preserve the original pairwise group Gram form. -/
theorem completedRepresentation_groupLeft_inner (g : G) (f h : Carrier μ α) (ξ η : H) :
    ⟪σ (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ,
      σ (p.toNonUnitalCompletion (groupLeft μ α g h)) η⟫_ℂ =
      ⟪σ (p.toNonUnitalCompletion f) ξ, σ (p.toNonUnitalCompletion h) η⟫_ℂ := by
  have hGram (a b : Carrier μ α) (x y : H) :
      ⟪σ (p.toNonUnitalCompletion a) x, σ (p.toNonUnitalCompletion b) y⟫_ℂ =
        ⟪x, σ (p.toNonUnitalCompletion (star a * b)) y⟫_ℂ := by
    have hproduct : σ (p.toNonUnitalCompletion (star a * b)) =
        star (σ (p.toNonUnitalCompletion a)) * σ (p.toNonUnitalCompletion b) := by
      rw [map_mul, map_mul, map_star, map_star]
    rw [hproduct]
    change ⟪σ (p.toNonUnitalCompletion a) x, σ (p.toNonUnitalCompletion b) y⟫_ℂ =
      ⟪x, star (σ (p.toNonUnitalCompletion a)) (σ (p.toNonUnitalCompletion b) y)⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  calc
    ⟪σ (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ,
        σ (p.toNonUnitalCompletion (groupLeft μ α g h)) η⟫_ℂ =
      ⟪ξ, σ (p.toNonUnitalCompletion (star (groupLeft μ α g f) * groupLeft μ α g h)) η⟫_ℂ :=
        hGram _ _ _ _
    _ = ⟪ξ, σ (p.toNonUnitalCompletion (star f * h)) η⟫_ℂ := by
      rw [star_groupLeft_mul_groupLeft]
    _ = ⟪σ (p.toNonUnitalCompletion f) ξ, σ (p.toNonUnitalCompletion h) η⟫_ℂ :=
      (hGram f h ξ η).symm

/-- Two arbitrary finite weighted source sums preserve their actual Hilbert inner product. -/
theorem inner_sum_completedRepresentation_groupLeft
    {ι : Type uI} {κ : Type uJ} (g : G) (s : Finset ι) (t : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (f : ι → Carrier μ α) (h : κ → Carrier μ α)
    (ξ : ι → H) (η : κ → H) :
    ⟪∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (groupLeft μ α g (f i))) (ξ i),
      ∑ j ∈ t, d j • σ (p.toNonUnitalCompletion (groupLeft μ α g (h j))) (η j)⟫_ℂ =
      ⟪∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (f i)) (ξ i),
        ∑ j ∈ t, d j • σ (p.toNonUnitalCompletion (h j)) (η j)⟫_ℂ := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z : ℂ => d i * z)
  apply Finset.sum_congr rfl
  intro j _
  rw [completedRepresentation_groupLeft_inner μ α p H σ g]

/-- Every finite weighted group-translated source sum has exactly its original Hilbert norm. -/
theorem norm_sum_completedRepresentation_groupLeft
    {ι : Type uI} (g : G) (s : Finset ι) (c : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) :
    ‖∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (groupLeft μ α g (f i))) (ξ i)‖ =
      ‖∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (f i)) (ξ i)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hInner := inner_sum_completedRepresentation_groupLeft μ α p H σ g s s c c f f ξ ξ
  simpa only [norm_sq_eq_re_inner (𝕜 := ℂ)] using congrArg (RCLike.re : ℂ → ℝ) hInner

end

end HaarTwistedCore
