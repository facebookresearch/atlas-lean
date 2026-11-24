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
public import MathlibExt.Analysis.CStarAlgebra.EssentialNondegeneracy
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.GramIntegratedIdentity

/-!
# The original nondegenerate covariant norm and its actual completion

The family consists of actual integrated seminorms of nondegenerate
covariant pairs in the source-sized Hilbert universe. The constructed
Gram norm model realizes every admissible seminorm by such a pair;
the original Haar coefficient bound gives the converse inclusion.

Reuse the already constructed intrinsic maximal C-star seminorm. Its
values are therefore the literal supremum of this original covariant
family, and every original Hilbert-universe integrated norm belongs to
that family. The same actual separated completion and canonical map
provide the completed C-star object. No new supremum or norm laws are
implemented, and faithfulness on the original source remains separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- Actual seminorms of original nondegenerate covariant pairs in the source-sized Hilbert universe. -/
def nondegenerateCovariantCStarSeminorms : Set (CStarSeminorm (Carrier μ α)) :=
  {p | ∃ (K : Type (max uG uA)) (_hK1 : NormedAddCommGroup K)
      (_hK2 : InnerProductSpace ℂ K) (_hK3 : CompleteSpace K)
      (π : CovariantRepresentation α K),
      π.algebra.essentialSpace = ⊤ ∧
        CovariantRepresentation.haarIntegratedCStarSeminorm μ π = p}

/-- The actual nondegenerate covariant family is exactly the original admissible seminorm family. -/
theorem nondegenerateCovariantCStarSeminorms_eq_admissible :
    nondegenerateCovariantCStarSeminorms μ α = admissibleCStarSeminorms μ α := by
  ext p
  constructor
  · rintro ⟨K, hK1, hK2, hK3, π, _hNondegenerate, hπ⟩
    let _ : NormedAddCommGroup K := hK1
    let _ : InnerProductSpace ℂ K := hK2
    let _ : CompleteSpace K := hK3
    rw [← hπ]
    exact CovariantRepresentation.haarIntegratedCStarSeminorm_mem_admissible μ π
  · intro hp
    obtain ⟨K, hK1, hK2, hK3, π, hNorm, hNondegenerate⟩ :=
      exists_admissibleCovariantNormModel_essentialSpace_eq_top μ α p hp
    let _ : NormedAddCommGroup K := hK1
    let _ : InnerProductSpace ℂ K := hK2
    let _ : CompleteSpace K := hK3
    refine ⟨K, hK1, hK2, hK3, π, hNondegenerate, ?_⟩
    apply CStarSeminorm.ext
    intro f
    exact (CovariantRepresentation.haarIntegratedCStarSeminorm_apply μ π f).trans (hNorm f)

/-- An original integrated norm in any Hilbert universe has a model in this nondegenerate family. -/
theorem haarIntegratedCStarSeminorm_mem_nondegenerateCovariantFamily
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : CovariantRepresentation α H) :
    CovariantRepresentation.haarIntegratedCStarSeminorm μ ρ ∈
      nondegenerateCovariantCStarSeminorms μ α := by
  rw [nondegenerateCovariantCStarSeminorms_eq_admissible]
  exact CovariantRepresentation.haarIntegratedCStarSeminorm_mem_admissible μ ρ

/-- The original full covariant gauge, using the same already computed maximal seminorm value. -/
def fullCovariantNorm (f : Carrier μ α) : ℝ := maximalCStarSeminorm μ α f

/-- Every full covariant value is the literal real supremum of the actual original pair norms. -/
theorem fullCovariantNorm_eq_sSup (f : Carrier μ α) :
    fullCovariantNorm μ α f =
      SupSet.sSup ((fun p : CStarSeminorm (Carrier μ α) => p f) ''
        nondegenerateCovariantCStarSeminorms μ α) := by
  rw [nondegenerateCovariantCStarSeminorms_eq_admissible]
  exact maximalCStarSeminorm_apply μ α f

/-- The original covariant C-star completion is the same actual maximal seminorm completion. -/
abbrev FullCovariantCompletion := (maximalCStarSeminorm μ α).NonUnitalCompletion

/-- The same constructed nonunital C-star dictionary on the actual full covariant completion. -/
@[instance_reducible]
def fullCovariantCompletionCStarAlgebra : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
  (maximalCStarSeminorm μ α).nonUnitalCompletionCStarAlgebra

/-- The original canonical full covariant map is the same actual source separation/completion map. -/
def toFullCovariantCompletion :
    let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
      fullCovariantCompletionCStarAlgebra μ α
    Carrier μ α →⋆ₙₐ[ℂ] FullCovariantCompletion μ α :=
  (maximalCStarSeminorm μ α).toNonUnitalCompletion

omit [μ.Regular] in
/-- Each canonical full completion image has the exact original full covariant norm. -/
theorem norm_toFullCovariantCompletion (f : Carrier μ α) :
    let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
      fullCovariantCompletionCStarAlgebra μ α
    ‖toFullCovariantCompletion μ α f‖ = fullCovariantNorm μ α f := by
  let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
    fullCovariantCompletionCStarAlgebra μ α
  exact (maximalCStarSeminorm μ α).norm_toNonUnitalCompletion f

omit [μ.Regular] in
/-- The original canonical core image is dense in this same full covariant completion. -/
theorem denseRange_toFullCovariantCompletion :
    let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
      fullCovariantCompletionCStarAlgebra μ α
    DenseRange (toFullCovariantCompletion μ α) :=
  (maximalCStarSeminorm μ α).denseRange_toNonUnitalCompletion

end

end HaarTwistedCore
