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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.CanonicalReducedAlgebra
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FullCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom

/-!
# Actual full-to-canonical-reduced homomorphism

The original canonical regular seminorm is bounded by the computed full
maximum. Extend its original codomain-restricted core map to the actual
full completion using the proved nonunital star-hom completion factory.
Every original full image keeps its same reduced operator value.
No model-independence, quotient or comparison result supplies these data.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace PointNormCStarAction

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.Regular] [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

/-- The actual full completion retains its already constructed nonunital C-star dictionaries. -/
local instance : NonUnitalCStarAlgebra (HaarTwistedCore.FullCovariantCompletion μ α) :=
  HaarTwistedCore.fullCovariantCompletionCStarAlgebra μ α

/-- The canonical reduced core map has its proved original full-norm bound. -/
theorem norm_toCanonicalReducedAlgebra_le_full (f : HaarTwistedCore.Carrier μ α) :
    ‖toCanonicalReducedAlgebra μ α f‖ ≤ HaarTwistedCore.maximalCStarSeminorm μ α f :=
  (norm_toCanonicalReducedAlgebra μ α f).trans_le (canonicalRegularSeminorm_le_maximal μ α f)

/-- The actual completed homomorphism from the full carrier to the fixed canonical reduced closure. -/
def fullToCanonicalReducedAlgebra : HaarTwistedCore.FullCovariantCompletion μ α →⋆ₙₐ[ℂ]
    CanonicalReducedAlgebra μ α :=
  (HaarTwistedCore.maximalCStarSeminorm μ α).fromNonUnitalCompletion
    (toCanonicalReducedAlgebra μ α) (norm_toCanonicalReducedAlgebra_le_full μ α)

/-- Every original full coefficient image retains its actual canonical reduced image. -/
@[simp]
theorem fullToCanonicalReducedAlgebra_apply (f : HaarTwistedCore.Carrier μ α) :
    fullToCanonicalReducedAlgebra μ α (HaarTwistedCore.toFullCovariantCompletion μ α f) =
      toCanonicalReducedAlgebra μ α f :=
  (HaarTwistedCore.maximalCStarSeminorm μ α).fromNonUnitalCompletion_apply
    (toCanonicalReducedAlgebra μ α) (norm_toCanonicalReducedAlgebra_le_full μ α) f

/-- The constructed full-to-reduced function is continuous in the actual C-star norm topologies. -/
theorem continuous_fullToCanonicalReducedAlgebra : Continuous (fullToCanonicalReducedAlgebra μ α) :=
  (HaarTwistedCore.maximalCStarSeminorm μ α).continuous_fromNonUnitalCompletion
    (toCanonicalReducedAlgebra μ α) (norm_toCanonicalReducedAlgebra_le_full μ α)

/-- The actual full map has dense range because its range contains every original reduced core image. -/
theorem denseRange_fullToCanonicalReducedAlgebra : DenseRange (fullToCanonicalReducedAlgebra μ α) := by
  have hrange : Set.range (toCanonicalReducedAlgebra μ α) ⊆
      Set.range (fullToCanonicalReducedAlgebra μ α) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨HaarTwistedCore.toFullCovariantCompletion μ α f,
      fullToCanonicalReducedAlgebra_apply μ α f⟩
  exact fun y => closure_mono hrange (denseRange_toCanonicalReducedAlgebra μ α y)

end

end PointNormCStarAction
