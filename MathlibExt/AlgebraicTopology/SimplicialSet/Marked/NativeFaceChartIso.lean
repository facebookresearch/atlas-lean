/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRelativeSimplexCharts

/-!
# Exact original single-face native chart isomorphisms

The original codimension-one face is its native standard simplex via
Mathlib's whole face isomorphism. Minimal marking and the exact base
restriction retain its original inclusion and every scalar operator.
The native chart comparison is straightening of that actual slice
isomorphism followed by the original native simplex unit mate.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire original codimension-one face over the base is the same minimal standard simplex with its actual
restricted base simplex. -/
def nativeSingleFaceBasisIso (B : SSet.{u}) (n : ℕ) (i : Fin (n + 2)) (σ : B _⦋n + 1⦌) :
    nativeSimplexBasis B n (B.map (SimplexCategory.δ i).op σ) ≅
      nativeSubcomplexBasis B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) :=
  Over.isoMk (minimal.mapIso (SSet.stdSimplex.faceSingletonComplIso i)) (by
    apply Hom.ext
    change (SSet.stdSimplex.faceSingletonComplIso i).hom ≫
        ((SSet.stdSimplex.face {i}ᶜ).ι ≫ SSet.yonedaEquiv.symm σ) =
      SSet.yonedaEquiv.symm (B.map (SimplexCategory.δ i).op σ)
    rw [← Category.assoc, SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    exact SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ i) σ)

/-- The original single-face inclusion square retains exactly its same whole native simplex coface map. -/
theorem nativeSingleFaceBasisIso_inclusion (B : SSet.{u}) (n : ℕ) (i : Fin (n + 2)) (σ : B _⦋n + 1⦌) :
    (nativeSingleFaceBasisIso B n i σ).hom ≫
        nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) =
      Over.homMk (minimal.map (SSet.stdSimplex.map (SimplexCategory.δ i)))
        (Hom.ext (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ i) σ)) := by
  apply Over.OverMorphism.ext
  apply Hom.ext
  exact SSet.stdSimplex.faceSingletonComplIso_hom_ι i

/-- The actual native whole codimension-one face chart is the original restricted simplex chart through its same
native image/unit isomorphism. -/
def nativeSingleFaceChartIso (B : SSet.{u}) (n : ℕ) (i : Fin (n + 2)) (σ : B _⦋n + 1⦌) :
    nativeSimplexChart B n (B.map (SimplexCategory.δ i).op σ) ≅
      nativeSubcomplexChart B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) :=
  (nativeSimplexImageIso B n (B.map (SimplexCategory.δ i).op σ)).symm ≪≫
    (nativeStraightening B).mapIso (nativeSingleFaceBasisIso B n i σ)

end SSet.Marked
