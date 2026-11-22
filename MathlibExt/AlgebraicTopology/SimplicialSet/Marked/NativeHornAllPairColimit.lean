/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornFaceColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeFaceChartIso

/-!
# The SAME original native horn face and full-intersection multispan

The existing original horn-colimit provider is retained unchanged.
Expose every actual original codimension-one face except the omitted
face, and every complete original ordered-pair intersection. Its genuine
original marked native colimit retains the whole actual source chart,
base projection and all original face/intersection injections.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual ORIGINAL native horn chart is straightening of the SAME original minimally marked horn carrier over
its unchanged full original base simplex. -/
def nativeOriginalHornChart {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    EnrichedDiagram (realization B)ᵒᵖ := nativeSubcomplexChart B (n + 1) σ (horn.{u} (n + 1) k)

/-- The original horn retains precisely its actual eligible original face indices and every complete ordered-pair
intersection. -/
abbrev nativeOriginalHornFaceSubcomplexDiagram {n : ℕ} (k : Fin (n + 2)) :
    Subcomplex.MulticoequalizerDiagram (horn.{u} (n + 1) k)
      (ι := ({k}ᶜ : Set (Fin (n + 2))))
      (fun i => SSet.stdSimplex.face {i.val}ᶜ)
      (fun i j => SSet.stdSimplex.face {i.val, j.val}ᶜ) :=
  SSet.horn.multicoequalizerDiagram k

/-- All actual ORIGINAL native eligible horn faces and original whole pair intersections give their SAME full native
chart multispan. -/
def nativeOriginalHornFaceChartSpan {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :=
  (nativeOriginalHornFaceSubcomplexDiagram.{u} k).multispanIndex.map (nativeSubcomplexChartFunctor B (n + 1) σ)

/-- The SAME original native horn chart has every literal original eligible face/intersection injection in its
complete multicofork. -/
def nativeOriginalHornFaceChartCocone {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    Multicofork (nativeOriginalHornFaceChartSpan B σ k) :=
  (nativeOriginalHornFaceSubcomplexDiagram.{u} k).multicofork.map (nativeSubcomplexChartFunctor B (n + 1) σ)

/-- The ORIGINAL native horn is genuinely colimiting for all its SAME original marked eligible faces and complete
original ordered-pair intersections. -/
def nativeOriginalHornFaceChartIsColimit {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    IsColimit (nativeOriginalHornFaceChartCocone B σ k) :=
  (Multicofork.isColimitMapEquiv _ _).toFun
    (nativeSubcomplexChartIsColimit B (n + 1) σ
      (nativeOriginalHornFaceSubcomplexDiagram.{u} k).multicofork
      ((Multicofork.isColimitMapEquiv _ Subcomplex.toSSetFunctor).symm
        (nativeOriginalHornFaceSubcomplexDiagram.{u} k).isColimit))

/-- Each SAME entire original coherent coface chart enters the actual original horn source through its original
whole face isomorphism and literal eligible multicofork injection. -/
def nativeOriginalHornCofaceChartMap {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k i : Fin (n + 2))
    (hi : i ≠ k) : nativeSimplexChart B n (B.δ i σ) ⟶ nativeOriginalHornChart B σ k :=
  (nativeSingleFaceChartIso B n i σ).hom ≫ (nativeOriginalHornFaceChartCocone B σ k).π
    ⟨i, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩

end SSet.Marked
