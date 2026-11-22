/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerRootFace
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootSourceMap

/-!
# Original root and base transports of lower native boundary coordinates

A positive omitted coface fixes the original root. The proved whole
coherent base-operator equation therefore gives the exact equality of
the original restricted and full base root objects. The actual native
boundary coface unit gives the whole lower root coefficient section;
all resulting marked transports use precisely that root equality.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original restricted native base root is exactly the same whole original base root whenever the omitted
coface vertex is positive. -/
theorem nativeLowerCofaceRootObject {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) =
      (EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  let x := op (SimplicialThickening.mk (⊥ : Vertex.{u} n))
  have h := congrArg (fun a : EnrichedFunctor SSet.{u} (Index.{u} n)ᵒᵖ (realization B)ᵒᵖ => a.obj x)
    (nativeChartIndex_comp_simplex B (SimplexCategory.δ j) σ)
  have hr := congrArg (fun i : Vertex.{u} (n + 1) =>
    (EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk i)))
      (coneCofaceEmbedding_root j hj)
  exact h.symm.trans hr

/-- Every actual marked coefficient target retains the same original native coface-root/base-root equality. -/
theorem nativeLowerCofaceRootTarget {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    F.obj ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) =
      F.obj ((EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) :=
  congrArg F.obj (nativeLowerCofaceRootObject B σ j hj)

/-- The original actual all-face boundary source has its whole marked coefficient at the unchanged original base
root. -/
def nativeBoundarySourceRootValue (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) : Marked.{u} :=
  (nativeSubcomplexChart B n σ (boundary n)).obj
    ((EnrichedFunctor.opposite (simplexInto B σ)).obj
      (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))))

/-- The same actual original native coface injection supplies its whole original smaller root-cone section in the
true boundary source. -/
def nativeLowerCofaceRootSection {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    coneWeight (⊥ : Vertex.{u} n) ⟶
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))).obj
        ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) :=
  (EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
      (coneDiagram n) (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
        (nativeBoundaryCofaceChartMap B n σ j)).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))

end SSet.Marked
