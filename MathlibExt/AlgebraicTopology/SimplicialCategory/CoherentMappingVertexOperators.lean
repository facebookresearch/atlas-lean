/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentEdgeVertexEvaluation

/-!
# All-height original vertex readback of coherent mapping operators

Restricting a supplied right-mapping simplex to any original front
vertex reads its literal two-endpoint Hom path at that image vertex and
the same last target. The entire path image, original object equalities
and scalar vertex maps are proved; no higher comparison is supplied.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingVertexOperators
open SimplicialEnrichment RightMappingSimplex HomSimplexEndpoints PathMaximumOperators PathEndpointTransport
open MappingEndpointPaths EdgeVertexEvaluation
variable {C : Carrier.{u}} {m : ℕ} (x y : C)

/-- The supplied mapping simplex is read at the literal original endpoint path of its selected front vertex
  and last target. -/
def endpointRead (θ : ⦋0⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋m⦌) :
    (x ⟶[SSet.{u}] y) _⦋0⦌ :=
  (EqualityTransport.hom (front_obj x y σ (θ.toOrderHom 0)) (last_obj x y σ)).app (op ⦋0⦌)
    (((toEnriched x y σ).map (.mk (ULift.up (θ.toOrderHom 0).castSucc)) (.mk (ULift.up (Fin.last (m +
      1))))).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (AdjacentHom.endpointPath (ULift.up.{u} (θ.toOrderHom 0).castSucc) (ULift.up
        (Fin.last (m + 1))) (Fin.le_last _))))

/-- The original Hom vertex readback follows every actual front-vertex operator with the literal endpoint
  path and exact object labels. -/
theorem read_operator (θ : ⦋0⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋m⦌) :
    MappingVertices.read x y ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex
      y)).map θ.op σ) = endpointRead x y θ σ := by
  let ν := (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)).map θ.op σ
  let S := toEnriched x y σ
  let G := coherentSimplexMap (extension θ)
  let a : coherentSimplex.{u} ⦋1⦌ := .mk (ULift.up 0)
  let b : coherentSimplex.{u} ⦋1⦌ := .mk (ULift.up 1)
  let c : coherentSimplex.{u} ⦋m + 1⦌ := .mk (ULift.up (θ.toOrderHom 0).castSucc)
  let d : coherentSimplex.{u} ⦋m + 1⦌ := .mk (ULift.up (Fin.last (m + 1)))
  have ha : G.obj a = c := congrArg SimplicialThickening.mk (lifted_front θ (0 : Fin 1))
  have hb : G.obj b = d := congrArg SimplicialThickening.mk (lifted_last θ)
  have hx : S.obj c = x := front_obj x y σ (θ.toOrderHom 0)
  have hy : S.obj d = y := last_obj x y σ
  let P : HomMappingCells.FixedSimplex x y (n := 0) :=
    ⟨G ≫ S, (congrArg S.obj ha).trans hx, (congrArg S.obj hb).trans hy⟩
  have hP : MappingVertices.fixedEdge x y ν = P := Subtype.ext (operator x y θ σ)
  have hR : MappingVertices.read x y ν = FixedEdgeReadback.readVertex x y P := congrArg
    (FixedEdgeReadback.readVertex x y) hP
  let U := G.map a b
  let V := S.map (G.obj a) (G.obj b)
  let Q := EqualityTransport.hom ha hb
  let Z := S.map c d
  let e₀ := EqualityTransport.hom ((congrArg S.obj ha).trans hx) ((congrArg S.obj hb).trans hy)
  let e₁ := EqualityTransport.hom hx hy
  have hV : V ≫ e₀ = Q ≫ Z ≫ e₁ := map_retarget x y S ha hb hx hy
  have hG : U ≫ Q = nerveMap (imageFunctor θ (0 : Fin 1)) := image_nerve θ (0 : Fin 1)
  have hWhole : (U ≫ V) ≫ e₀ = nerveMap (imageFunctor θ (0 : Fin 1)) ≫ (Z ≫ e₁) :=
    (Category.assoc U V e₀).trans
      ((congrArg (fun f => U ≫ f) hV).trans
        ((Category.assoc U Q (Z ≫ e₁)).symm.trans (congrArg (fun f => f ≫ (Z ≫ e₁)) hG)))
  let p := ComposableArrows.mk₀ (AdjacentHom.endpointPath (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide))
  have hCell := congrArg (fun f => f.app (op ⦋0⦌) p) hWhole
  have hImage := image_zero_flag.{u} θ
  rw [zero_flag] at hImage
  have hPath : (nerveMap (imageFunctor θ (0 : Fin 1))).app (op ⦋0⦌) p =
      ComposableArrows.mk₀ (AdjacentHom.endpointPath (ULift.up.{u} (θ.toOrderHom 0).castSucc) (ULift.up
        (Fin.last (m + 1))) (Fin.le_last _)) :=
    (nerveMap_app_mk₀ _ _).trans (congrArg ComposableArrows.mk₀ hImage)
  have hLast := congrArg (fun p => (e₁.app (op ⦋0⦌)) ((Z.app (op ⦋0⦌)) p)) hPath
  exact hR.trans ((read_fixed x y P).trans (hCell.trans hLast))

end CategoryTheory.CoherentRealization.MappingVertexOperators
