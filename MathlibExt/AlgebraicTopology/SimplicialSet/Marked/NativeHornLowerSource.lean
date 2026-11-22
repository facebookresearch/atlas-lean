/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornPositiveSource
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootBoundaryInverse

/-!
# Original lower coordinates in the original native horn source

Each eligible positive coface supplies its complete original smaller
root-cone section through the actual native left Kan unit. The original
marked lower-coordinate isomorphism and the same proved coface-root
equality give the entire lower source map. The literal native inclusion
in the full boundary recovers the original whole lower inverse, including
its unchanged original base-object transport.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every eligible original coface supplies its whole smaller root-cone section in the original native partial horn
source. -/
def nativeHornLowerCofaceRootSection {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hjk : j ≠ k) :
    coneWeight (⊥ : Vertex.{u} n) ⟶
      (nativeOriginalHornChart B σ k).obj
        ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) :=
  (EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
      (coneDiagram n) (nativeOriginalHornChart B σ k)
        (nativeOriginalHornCofaceChartMap B σ k j hjk)).app
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))

/-- The complete original lower-coface unit section retains the same whole boundary section under the literal native
horn inclusion. -/
theorem nativeHornLowerCofaceRootSection_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeHornLowerCofaceRootSection B σ k j hjk ≫
      (nativeOriginalHornToBoundary B σ k).app
        ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) =
        nativeLowerCofaceRootSection B σ j := by
  let f := EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))
  let W := coneDiagram n
  let U := EnrichedLeftKan.universalHomEquiv f W
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
  have h := (EnrichedLeftKan.universalHomEquiv_natural_right f W
    (nativeOriginalHornCofaceChartMap B σ k j hjk) (nativeOriginalHornToBoundary B σ k)).symm.trans
      (congrArg U (nativeOriginalHornToBoundary_coface B σ k j hjk))
  exact congrArg (fun a => a.app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) h

/-- The same original coface-root equality transports the actual whole native horn coefficient and its literal
inclusion in the boundary. -/
theorem nativeHornLowerRootTransport_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hj : 0 < j) :
    eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeOriginalHornChart B σ k)) ≫
      (nativeOriginalHornToBoundary B σ k).app
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
    (nativeOriginalHornToBoundary B σ k).app
      ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) ≫
      eqToHom (nativeLowerCofaceRootTarget B σ j hj
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))) := by
  have h (x y : (realization B)ᵒᵖ) (e : x = y) :
      eqToHom (congrArg (nativeOriginalHornChart B σ k).obj e) ≫
        (nativeOriginalHornToBoundary B σ k).app y =
      (nativeOriginalHornToBoundary B σ k).app x ≫
        eqToHom (congrArg (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))).obj e) := by
    subst y
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  exact h _ _ (nativeLowerCofaceRootObject B σ j hj)

/-- The entire original marked eligible lower coordinate enters the original native horn source through its actual
coface unit and unchanged full base transport. -/
def nativeHornLowerInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hj : 0 < j) (hjk : j ≠ k) :
    coneLowerRootFaceWeight.{u} j ⟶ nativeOriginalHornSourceRootValue B σ k :=
  ((coneLowerRootFaceIso j hj).inv ≫ nativeHornLowerCofaceRootSection B σ k j hjk) ≫
    eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeOriginalHornChart B σ k))

/-- Every entire original eligible lower-coordinate source inverse retains the same original full boundary inverse
and original coface-root transport. -/
theorem nativeHornLowerInverse_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hj : 0 < j) (hjk : j ≠ k) :
    nativeHornLowerInverse B σ k j hj hjk ≫
      (nativeOriginalHornToBoundary B σ k).app
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      nativeLowerRootBoundaryInverse B σ j hj := by
  let e := (coneLowerRootFaceIso j hj).inv
  let s := nativeHornLowerCofaceRootSection B σ k j hjk
  let t := eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeOriginalHornChart B σ k))
  let t' := eqToHom (nativeLowerCofaceRootTarget B σ j hj
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))))
  let μ := (nativeOriginalHornToBoundary B σ k).app
    ((EnrichedFunctor.opposite (simplexInto B σ)).obj
      (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))))
  let μ' := (nativeOriginalHornToBoundary B σ k).app
    ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
      (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))))
  have ht : t ≫ μ = μ' ≫ t' := nativeHornLowerRootTransport_boundary B σ k j hj
  have hs : s ≫ μ' = nativeLowerCofaceRootSection B σ j :=
    nativeHornLowerCofaceRootSection_boundary B σ k j hjk
  exact (Category.assoc (e ≫ s) t μ).trans
    ((congrArg (fun f => (e ≫ s) ≫ f) ht).trans
      ((Category.assoc (e ≫ s) μ' t').symm.trans
        ((congrArg (fun f => f ≫ t') (Category.assoc e s μ')).trans
          (congrArg (fun f => (e ≫ f) ≫ t') hs))))

end SSet.Marked
