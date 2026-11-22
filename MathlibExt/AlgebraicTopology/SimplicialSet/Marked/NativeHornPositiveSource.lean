/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootHornBoundaryComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUpperRootInverseUnit

/-!
# The SAME original positive chart inside the ORIGINAL native partial horn source

The genuine original zeroth-face tail source Iso and the literal eligible
face0 injection give the complete original positive source map. The SAME
whole unit mate retains its original positive coefficient section and
every original upper coordinate. The actual horn-to-boundary comparison
recovers exactly the original full-boundary positive and upper maps;
lower-coordinate and entire source gluing remain separate conclusions.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The ORIGINAL native partial horn source retains its SAME full original marked coefficient at the unchanged full
base root. -/
def nativeOriginalHornSourceRootValue {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) : Marked.{u} :=
  (nativeOriginalHornChart B σ k).obj ((EnrichedFunctor.opposite (simplexInto B σ)).obj
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))))

/-- The SAME genuine original positive tail source inverse enters the actual ORIGINAL native horn through its
literal eligible face0 injection. -/
def nativeHornPositiveInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) (hk : 0 < k) :
    nativePositiveRootChart B (n + 1) σ ⟶ nativeOriginalHornChart B σ k :=
  (nativeTailFaceSourceIso B n σ).inv ≫ nativeOriginalHornCofaceChartMap B σ k 0 (ne_of_lt hk)

/-- The entire original positive horn-source map retains exactly the SAME original whole boundary positive inverse
under the literal native source comparison. -/
theorem nativeHornPositiveInverse_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornPositiveInverse B σ k hk ≫ nativeOriginalHornToBoundary B σ k = nativeBoundaryPositiveInverse B n σ :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (nativeTailFaceSourceIso B n σ).inv ≫ f)
      (nativeOriginalHornToBoundary_coface B σ k 0 (ne_of_lt hk)))

/-- The SAME entire original positive source section is the actual whole original unit mate into the original native
partial horn coefficient diagram. -/
def nativeHornPositiveSection {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) (hk : 0 < k) :
    coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj (nativeOriginalHornChart B σ k) :=
  EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
    (coneAfterDiagram (⊥ : Vertex.{u} (n + 1))) (nativeOriginalHornChart B σ k) (nativeHornPositiveInverse B σ k hk)

/-- The full original positive source section retains exactly its SAME complete original boundary section under the
actual original comparison. -/
theorem nativeHornPositiveSection_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornPositiveSection B σ k hk ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map (nativeOriginalHornToBoundary B σ k) =
        nativePositiveRootBoundarySection B σ := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let U := EnrichedLeftKan.universalHomEquiv j W (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
  exact (EnrichedLeftKan.universalHomEquiv_natural_right j W
    (nativeHornPositiveInverse B σ k hk) (nativeOriginalHornToBoundary B σ k)).symm.trans
      (congrArg U (nativeHornPositiveInverse_boundary B σ k hk))

/-- Every complete original marked upper coordinate enters the ORIGINAL native horn source through the SAME whole
original positive section. -/
def nativeHornUpperInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (j : Fin (n + 2)) (hj : 0 < j) :
    coneUpperFaceMarked (⊥ : Vertex.{u} (n + 1)) (ULift.up j) ⟶ nativeOriginalHornSourceRootValue B σ k :=
  coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩ ≫
    (nativeHornPositiveSection B σ k hk).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))

/-- Every SAME original entire upper-coordinate inverse retains its exact original boundary inverse under the actual
native horn coefficient comparison. -/
theorem nativeHornUpperInverse_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (j : Fin (n + 2)) (hj : 0 < j) :
    nativeHornUpperInverse B σ k hk j hj ≫
      (nativeOriginalHornToBoundary B σ k).app ((EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) = nativeUpperRootBoundaryInverse B σ j hj :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
      ⟨ULift.up j, hj⟩ ≫ f)
        (congrArg (fun a => a.app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))))
          (nativeHornPositiveSection_boundary B σ k hk)))

end SSet.Marked
