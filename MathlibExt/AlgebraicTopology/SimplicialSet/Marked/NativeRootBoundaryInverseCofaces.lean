/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryInverseCofaceValues

/-!
# Every original coface recovered by the full native boundary inverse

The original zeroth coface retains its genuine whole tail inverse. Each
positive omitted coface retains its original root and every original
positive marked coefficient under the same full enriched inverse. The
actual native adjunction therefore recovers every unchanged original
boundary coface map, including the zero-dimensional coface case.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every positive omitted coface has exactly its unchanged original full enriched source section under the genuine
entire boundary inverse. -/
theorem nativeRootBoundaryInverseCofaceSection_eq (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) (hk : 0 < k) :
    nativeRootBoundaryInverseCofaceSection B n σ k =
      EnrichedLeftKan.universalHomEquiv
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))) (coneDiagram n)
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeBoundaryCofaceChartMap B n σ k) := by
  apply EnrichedDiagramMap.ext
  funext i
  change (nativeRootBoundaryInverseCofaceSection B n σ k).app
      (op (SimplicialThickening.mk i.unop.as)) =
    (EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))) (coneDiagram n)
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeBoundaryCofaceChartMap B n σ k)).app
        (op (SimplicialThickening.mk i.unop.as))
  by_cases hi : i.unop.as = (⊥ : Vertex.{u} n)
  · rw [hi]
    exact nativeRootBoundaryInverseCofaceSection_root B n σ k hk
  · have hpos : (⊥ : Vertex.{u} n) < i.unop.as := lt_of_le_of_ne bot_le (Ne.symm hi)
    cases n with
    | zero =>
      have he : i.unop.as = (⊥ : Vertex.{u} 0) := ULift.ext (Fin.eq_zero i.unop.as.down)
      exact False.elim (hi he)
    | succ n =>
      exact nativeRootBoundaryInverseCofaceSection_positive B n σ k hk i hpos

/-- The same genuine full native chart inverse recovers every unchanged original boundary coface map, with the whole
original root, positive coefficients and attaching data retained. -/
theorem nativeRootBoundaryChartInverse_coface (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeRootBoundaryCofaceMap B n σ k ≫ nativeRootBoundaryChartInverse B n σ =
      nativeBoundaryCofaceChartMap B n σ k := by
  by_cases hk : k = 0
  · subst k
    let e := nativeTailFaceSourceIso B n σ
    have h₁ := congrArg (fun q => q ≫ nativeRootBoundaryChartInverse B n σ)
      (nativeTailFaceSourceIso_rootBoundary B n σ).symm
    have h₂ : (e.hom ≫ nativePositiveRootBoundaryMap B (n + 1) σ) ≫ nativeRootBoundaryChartInverse B n σ =
        e.hom ≫ nativeBoundaryPositiveInverse B n σ :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => e.hom ≫ q) (nativeRootBoundaryChartInverse_positive B n σ))
    exact h₁.trans (h₂.trans (e.hom_inv_id_assoc (nativeBoundaryCofaceChartMap B n σ 0)))
  · have hpos : (0 : Fin (n + 2)) < k := lt_of_le_of_ne (Fin.zero_le k) (Ne.symm hk)
    apply (EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))) (coneDiagram n)
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))).injective
    exact (nativeRootBoundaryInverseCofaceSection_homEquiv B n σ k).trans
      (nativeRootBoundaryInverseCofaceSection_eq B n σ k hpos)

end SSet.Marked
