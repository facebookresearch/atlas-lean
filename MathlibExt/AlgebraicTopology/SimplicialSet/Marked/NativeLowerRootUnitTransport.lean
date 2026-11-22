/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootBoundarySourceTransport

/-!
# Actual original lower root-coordinate unit transport

The whole original coherent base transport, evaluated at the original
coface root, composes with its proved same-base root equality to exactly
the original root-vertex transport. The supported proper coface unit
therefore reads the genuine marked lower root-coordinate inclusion
followed by the unchanged full native root-boundary unit.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private theorem indexEqToHom_component (n : ℕ)
    {F G : EnrichedDiagram (Index.{u} n)ᵒᵖ} (h : F = G) (i : Vertex.{u} n) :
    (eqToHom h).app (op (SimplicialThickening.mk i)) =
      eqToHom (congrArg (fun V : EnrichedDiagram (Index.{u} n)ᵒᵖ =>
        V.obj (op (SimplicialThickening.mk i))) h) := by
  cases h
  rfl

/-- The same complete original base-restriction transport at a lower coface root composes to precisely the original
root-vertex coefficient transport. -/
theorem nativeLowerRootUnitTransport {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ)).app F).app
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) ≫
        eqToHom (nativeLowerCofaceRootTarget B σ j hj F) =
      eqToHom (congrArg (fun i : Vertex.{u} (n + 1) =>
        F.obj ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk i))))
          (coneCofaceEmbedding_root j hj)) := by
  let h := nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ
  let x := op (SimplicialThickening.mk (⊥ : Vertex.{u} n))
  let hF := Functor.congr_obj h F
  let h₀ := congrArg (fun V : EnrichedDiagram (Index.{u} n)ᵒᵖ => V.obj x) hF
  let h₁ := nativeLowerCofaceRootTarget B σ j hj F
  have hp : ((eqToHom h).app F).app x = eqToHom h₀ :=
    (congrArg (fun a => a.app x) (eqToHom_app h F)).trans
      (indexEqToHom_component n hF (⊥ : Vertex.{u} n))
  exact (congrArg (fun a => a ≫ eqToHom h₁) hp).trans (eqToHom_trans h₀ h₁)

/-- The entire original proper lower-coface section, after its exact root/base transport, is the genuine lower
coordinate chart and unchanged original native root-boundary unit. -/
theorem nativeLowerRootProperSection_unit {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    (nativeProperBoundaryFaceSection B (SimplexCategory.δ j) σ
        (coneCofaceEmbedding_not_surjective j)).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) ≫
        eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeRootBoundaryChart B (n + 1) σ)) =
      ((coneLowerRootFaceIso j hj).hom ≫ coneLowerRootFaceToBoundary j hj) ≫
        (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
          (coneRootBoundaryDiagram (n + 1))).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  let k := EnrichedFunctor.opposite (simplexInto B σ)
  let F := nativeRootBoundaryChart B (n + 1) σ
  let h := coneCofaceEmbedding_root.{u} j hj
  let i := coneCofaceEmbedding j (⊥ : Vertex.{u} n)
  let η := EnrichedLeftKan.unit k (coneRootBoundaryDiagram (n + 1))
  let s := coneProperBoundaryImage (coneCofaceEmbedding j).toOrderHom
    (coneCofaceEmbedding_not_surjective j) (⊥ : Vertex.{u} n)
  let t := ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ)).app F).app
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
  let v := eqToHom (nativeLowerCofaceRootTarget B σ j hj F)
  let w := eqToHom (congrArg (fun a : Vertex.{u} (n + 1) =>
    F.obj (k.obj (op (SimplicialThickening.mk a)))) h)
  let r := eqToHom (congrArg (fun a : Vertex.{u} (n + 1) => coneRootBoundaryMarked a) h)
  let u := fun a : Vertex.{u} (n + 1) => η.app (op (SimplicialThickening.mk a))
  have ht : t ≫ v = w := nativeLowerRootUnitTransport B σ j hj F
  have hu : u i ≫ w = r ≫ u (⊥ : Vertex.{u} (n + 1)) := eqToHom_naturality u h
  have hs : s ≫ r = (coneLowerRootFaceIso j hj).hom ≫ coneLowerRootFaceToBoundary j hj :=
    (coneLowerRootFaceIso_boundary j hj).symm
  change ((s ≫ u i) ≫ t) ≫ v = _
  exact (Category.assoc (s ≫ u i) t v).trans
    ((congrArg (fun a => (s ≫ u i) ≫ a) ht).trans
      ((Category.assoc s (u i) w).trans
        ((congrArg (fun a => s ≫ a) hu).trans
          ((Category.assoc s r (u (⊥ : Vertex.{u} (n + 1)))).symm.trans
            (congrArg (fun a => a ≫ u (⊥ : Vertex.{u} (n + 1))) hs)))))

end SSet.Marked
