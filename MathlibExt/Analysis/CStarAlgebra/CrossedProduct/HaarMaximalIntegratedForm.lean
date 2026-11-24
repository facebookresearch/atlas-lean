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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom

/-!
# The original integrated representation on the actual intrinsic maximal completion

The actual integrated seminorm is bounded by the computed intrinsic
maximum on the original Haar core. Use the same bounded nonunital
star-hom separation/completion extension on that exact maximum. Its
canonical source images retain the literal original Haar vector integral.

The construction permits an arbitrary independent Hilbert universe and
requires no supplied completed representation. The identification of this
intrinsic seminorm with all nondegenerate covariant norms and the faithful
full crossed-product source statement remain separate obligations.
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

/-- The original Haar integrated map extended to the same intrinsic maximal seminorm completion. -/
def haarMaximalIntegratedHom :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H) := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  exact p.fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ)

/-- Every original coefficient retains its actual integrated operator value. -/
theorem haarMaximalIntegratedHom_apply (f : HaarTwistedCore.Carrier μ α) :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    haarMaximalIntegratedHom μ ρ (p.toNonUnitalCompletion f) = haarIntegratedHom μ ρ f := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change p.fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ) (p.toNonUnitalCompletion f) = _
  exact p.fromNonUnitalCompletion_apply (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ) f

/-- The completed source image acts by the literal original Haar vector integral. -/
theorem haarMaximalIntegratedHom_apply_vector (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    haarMaximalIntegratedHom μ ρ (p.toNonUnitalCompletion f) ξ =
      ∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact (congrArg (fun T : H →L[ℂ] H => T ξ) (haarMaximalIntegratedHom_apply μ ρ f)).trans
    (haarIntegratedHom_apply_vector μ ρ f ξ)

/-- The constructed original completed representation is continuous in that completion's norm. -/
theorem continuous_haarMaximalIntegratedHom :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Continuous (haarMaximalIntegratedHom μ ρ) := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change Continuous (p.fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ))
  exact p.continuous_fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ)

end

end CovariantRepresentation
