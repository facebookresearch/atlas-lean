/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeConcreteImageIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.BoundaryCells

/-!
# Whole native relative simplex charts

Every actual original subcomplex of a simplex retains its full minimal
marking and original composite map to the base. Its native straightening
is the original whole chart colimit. The attaching map is the actual
straightened inclusion followed by the exact unit-mate simplex chart
isomorphism. Boundaries and every horn specialize this same construction;
no relative cofibration or weak-equivalence outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole original minimal marked simplex subcomplex lies over the same original base simplex. -/
def nativeSubcomplexBasis (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (A : (Δ[n] : SSet.{u}).Subcomplex) : Over (max B) :=
  Over.mk (toMax (A.ι ≫ SSet.yonedaEquiv.symm σ) : min (A : SSet.{u}) ⟶ max B)

/-- The complete original subcomplex inclusion is its exact marked map over the unchanged original base. -/
def nativeSubcomplexInclusion (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    nativeSubcomplexBasis B n σ A ⟶ nativeSimplexBasis B n σ :=
  Over.homMk (minimal.map A.ι) (Hom.ext rfl)

/-- The original relative chart retains the complete native marked chart-colimit source, with no replacement object. -/
def nativeSubcomplexChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (A : (Δ[n] : SSet.{u}).Subcomplex) : EnrichedDiagram (realization B)ᵒᵖ :=
  (nativeStraightening B).obj (nativeSubcomplexBasis B n σ A)

/-- The full relative chart attaching map is exactly straightening of the original subcomplex inclusion
  followed by its original simplex unit-mate comparison. -/
def nativeSubcomplexChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    nativeSubcomplexChart B n σ A ⟶ nativeSimplexChart B n σ :=
  (nativeStraightening B).map (nativeSubcomplexInclusion B n σ A) ≫
    (nativeSimplexImageIso B n σ).hom

/-- The original chart attaching map retains its precise source-inclusion and native unit equation under the
  whole adjunction. -/
theorem nativeSubcomplexChartMap_homEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (nativeStraighteningAdjunction B).homEquiv _ _ (nativeSubcomplexChartMap B n σ A) =
      nativeSubcomplexInclusion B n σ A ≫
        nativeSimplexChartHomEquiv B n σ (nativeSimplexChart B n σ) (𝟙 _) := by
  exact ((nativeStraighteningAdjunction B).homEquiv_naturality_left
    (nativeSubcomplexInclusion B n σ A) (nativeSimplexImageIso B n σ).hom).trans
      (congrArg (fun f => nativeSubcomplexInclusion B n σ A ≫ f)
        (nativeSimplexImageIso_homEquiv B n σ))

/-- The entire original boundary attaching chart, at the original value universe and base simplex. -/
def nativeBoundaryChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativeSubcomplexChart B n σ (boundary n) ⟶ nativeSimplexChart B n σ :=
  nativeSubcomplexChartMap B n σ (boundary n)

/-- Every original horn attaching chart retains its actual horn index and full source subcomplex. -/
def nativeHornChartMap (B : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) (σ : B _⦋n⦌) :
    nativeSubcomplexChart B n σ (horn n i) ⟶ nativeSimplexChart B n σ :=
  nativeSubcomplexChartMap B n σ (horn n i)

end SSet.Marked
