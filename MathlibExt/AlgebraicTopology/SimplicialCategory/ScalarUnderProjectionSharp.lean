/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderOperatorWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderRowSharp
import MathlibExt.AlgebraicTopology.SimplicialSet.RezkSharpComparisonBridge

/-!
# Sharpness of the actual full original scalar-under projection

All full original rows and all original relative ordinal comparisons
satisfy the actual Rezk diagonal theorem. The canonical diagonal
transpose isomorphisms preserve the entire original forgetful projection.
The conclusion retains the same original total, base, words and maps.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The SAME original transposed projection has sharp diagonal and every
actual original Rezk comparison is weak, with all ordinal arities retained. -/
theorem transposedProjection_sharp_and_kappa_weak
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)] (z : C) :
    MorphismProperty.sharpMaps realizationWeakEquivalences
        (simplicialDiagonalFunctor.map (simplicialTransposeFunctor.map (nerveProjection C z))) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)),
        WeakEquivalence (RezkOriginal61.kappa
          (simplicialTransposeFunctor.map (nerveProjection C z)) n v) := by
  apply rezk_diagonal_sharp_and_original_kappa
  · intro n
    exact rowProjection_sharp C z n.len
  · intro n m f
    exact (weakEquivalence_iff _).mpr (rowRelativeComparison_weak C z f)

/-- The actual entire original scalar-under forgetful projection is sharp
for the SAME original component groupoid, without any original Kan premise. -/
theorem projection_sharp
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)] (z : C) :
    MorphismProperty.sharpMaps realizationWeakEquivalences (projection C z) := by
  let e : Arrow.mk (simplicialDiagonalFunctor.map
      (simplicialTransposeFunctor.map (nerveProjection C z))) ≅ Arrow.mk (projection C z) :=
    Arrow.isoMk' _ _ (simplicialDiagonalTransposeIso (nerveDiagram C z))
      (simplicialDiagonalTransposeIso (baseNerveDiagram C))
      (simplicialDiagonalTransposeIso_naturality (nerveProjection C z)).symm
  exact (MorphismProperty.sharpMaps realizationWeakEquivalences).arrow_mk_iso_iff e |>.mp
    (transposedProjection_sharp_and_kappa_weak C z).1

/-- Every literal original native simplex transition of the full actual
under-nerve projection is weak, including all original operators. -/
theorem projection_simplexTransition_weak
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)]
    (z : C) {s t : SimplexIndex (baseTotal C)} (a : s ⟶ t) :
    realizationWeakEquivalences ((simplexPullbackDiagram (projection C z)).map a) :=
  (sharpMaps_iff_simplexPullbackTransitions (projection C z)).mp (projection_sharp C z) a

/-- The SAME original projection satisfies the full native homotopy-pullback
comparison definition of sharpness, without changing its spectra of words or coefficients. -/
theorem projection_originalComparisonSharp
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)] (z : C) :
    SharpComparisonDraft.Sharp (projection C z) :=
  (sharpMaps_iff_originalComparisonSharp (projection C z)).mp (projection_sharp C z)

end SSet.ScalarUnderCategory
