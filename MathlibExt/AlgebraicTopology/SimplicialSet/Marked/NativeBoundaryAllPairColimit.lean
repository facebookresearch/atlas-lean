/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryFaceColimit

/-!
# The original native full-pair boundary chart multispan

The existing original boundary provider retains every codimension-one
face and full pairwise intersection. This exposes its entire native
multispan and cocone on all ordered pairs, using the original minimal
marking, base projection and genuine chart-colimit preservation.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The unchanged original scalar boundary provider retains every original face and complete pairwise intersection
label. -/
abbrev nativeBoundaryFaceSubcomplexDiagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (boundary.{u} (n + 1))
      (fun i : Fin (n + 2) => SSet.stdSimplex.face {i}ᶜ)
      (fun i j => SSet.stdSimplex.face {i, j}ᶜ) :=
  SSet.boundary.multicoequalizerDiagram (n + 1)

/-- All actual original boundary faces and intersections form their unchanged whole native chart multispan. -/
def nativeBoundaryFaceChartSpan (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :=
  (nativeBoundaryFaceSubcomplexDiagram.{u} n).multispanIndex.map
    (nativeSubcomplexChartFunctor B (n + 1) σ)

/-- The original native boundary chart has its entire original face/intersection cocone. -/
def nativeBoundaryFaceChartCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    Multicofork (nativeBoundaryFaceChartSpan B n σ) :=
  (nativeBoundaryFaceSubcomplexDiagram.{u} n).multicofork.map
    (nativeSubcomplexChartFunctor B (n + 1) σ)

/-- The native original boundary is genuinely colimiting for all of its same whole marked face charts and original
intersections. -/
def nativeBoundaryFaceChartIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    IsColimit (nativeBoundaryFaceChartCocone B n σ) :=
  (Multicofork.isColimitMapEquiv _ _).toFun
    (nativeSubcomplexChartIsColimit B (n + 1) σ
      (nativeBoundaryFaceSubcomplexDiagram.{u} n).multicofork
      ((Multicofork.isColimitMapEquiv _ Subcomplex.toSSetFunctor).symm
        (nativeBoundaryFaceSubcomplexDiagram.{u} n).isColimit))

end SSet.Marked
