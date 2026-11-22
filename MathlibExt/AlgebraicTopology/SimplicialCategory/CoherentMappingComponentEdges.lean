/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingOneFlags
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingVertexOperators
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Actual original Hom edges read from coherent right mapping spaces

A supplied edge of the genuine right mapping space reads an actual
original Hom edge with the same two individual Hom vertices. The source
uses the zero flag and the target uses original union composition with
the proved front identity. No Kan or weak-comparison outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingComponentEdges
open SimplicialEnrichment RightMappingSimplex MappingFlagVertices MappingOneFlags
open PathLastMaximum PathMaximumFlags AdjacentHom
variable {C : Carrier.{u}} (x y : C)

private theorem scalar_face {H : SSet.{u}} (η : (Δ[1] : SSet.{u}) ⟶ H)
    (j k : Fin 2) (hjk : (SimplexCategory.δ j).toOrderHom 0 = k) :
    H.δ j (SSet.yonedaEquiv η) = η.app (op ⦋0⦌) (standardVertex.{u} k) := by
  have hδ : SimplexCategory.δ j = SimplexCategory.const ⦋0⦌ ⦋1⦌ k := by
    ext i : 3
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hjk
  have hV : SSet.yonedaEquiv (SSet.stdSimplex.δ j : (Δ[0] : SSet.{u}) ⟶ Δ[1]) = standardVertex.{u} k :=
    (SSet.yonedaEquiv_map (SimplexCategory.δ j)).trans (congrArg (fun f => SSet.stdSimplex.objEquiv.symm f) hδ)
  exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ j) η).trans
    ((SSet.yonedaEquiv_comp (SSet.stdSimplex.δ j) η).trans (congrArg (fun v => η.app (op ⦋0⦌) v) hV))

/-- The actual Hom edge read from a supplied mapping-space edge retains its original source Hom vertex. -/
theorem read_source (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋1⦌) :
    (x ⟶[SSet.{u}] y).δ 1 (readSimplex x y σ) =
      MappingVertices.read x y ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
        (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)).δ 1 σ) := by
  let S := toEnriched x y σ
  let h₀ := front_obj x y σ (0 : Fin 2)
  let h₂ := last_obj x y σ
  let η := HomFlagEvaluation.evaluate x y S h₀ h₂
  have hE := evaluate_vertex x y S h₀ h₂ (0 : Fin 2)
  have hF := zero_flag.{u} (n := 1)
  have hP := congrArg (fun p => (EqualityTransport.hom h₀ h₂).app (op ⦋0⦌)
    ((S.map (.mk (ULift.up (0 : Fin 3))) (.mk (ULift.up (2 : Fin 3)))).app (op ⦋0⦌) (ComposableArrows.mk₀ p))) hF
  have hR := MappingVertexOperators.read_operator x y (SimplexCategory.δ (1 : Fin 2)) σ
  exact (scalar_face η 1 0 rfl).trans (hE.trans (hP.trans hR.symm))

/-- The actual Hom edge read from a supplied mapping-space edge retains its original target Hom vertex
  through the genuine front identity and whole union composition. -/
theorem read_target (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋1⦌) :
    (x ⟶[SSet.{u}] y).δ 0 (readSimplex x y σ) =
      MappingVertices.read x y ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
        (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)).δ 0 σ) := by
  let S := toEnriched x y σ
  let a : coherentSimplex.{u} ⦋2⦌ := .mk (ULift.up 0)
  let b : coherentSimplex.{u} ⦋2⦌ := .mk (ULift.up 1)
  let c : coherentSimplex.{u} ⦋2⦌ := .mk (ULift.up 2)
  let h₀ := front_obj x y σ (0 : Fin 2)
  let h₁ := front_obj x y σ (1 : Fin 2)
  let h₂ := last_obj x y σ
  let p := ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up (1 : Fin 3)) (by decide))
  let q := ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (1 : Fin 3)) (ULift.up (2 : Fin 3)) (by decide))
  let η := HomFlagEvaluation.evaluate x y S h₀ h₂
  let V := S.map a c ≫ EqualityTransport.hom h₀ h₂
  let U := S.map a b ≫ EqualityTransport.hom h₀ h₁
  let W := S.map b c ≫ EqualityTransport.hom h₁ h₂
  have hE := evaluate_vertex x y S h₀ h₂ (1 : Fin 2)
  have hC := mapped_composition S a b c h₀ h₁ h₂
  have hCell := congrArg (fun f => f.app (op ⦋0⦌) (p, q)) hC
  have hUnion : (eComp SSet.{u} a b c).app (op ⦋0⦌) (p, q) = ComposableArrows.mk₀
      (compose (0 : Fin 2) 1
        (endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up (1 : Fin 3)) (by decide))
        (endpointPath (ULift.up.{u} (1 : Fin 3)) (ULift.up (2 : Fin 3)) (by decide))) := by
    change p.prod' q ⋙ SimplicialThickening.compFunctor (SimplicialThickening.mk (ULift.up.{u} (0 : Fin 3)))
      (SimplicialThickening.mk (ULift.up (1 : Fin 3))) (SimplicialThickening.mk (ULift.up (2 : Fin 3))) = _
    exact ComposableArrows.ext₀ rfl
  have hFlag : ComposableArrows.mk₀ (flag.{u} (1 : Fin 2)) = (eComp SSet.{u} a b c).app (op ⦋0⦌) (p, q) :=
    (congrArg ComposableArrows.mk₀ (one_flag.{u})).symm.trans hUnion.symm
  have hPrefix : U.app (op ⦋0⦌) p = (eId SSet.{u} x).app (op ⦋0⦌) PUnit.unit := front_identity C x y σ
  have hUnit := congr($(e_id_comp SSet.{u} x y).app (op ⦋0⦌) (W.app (op ⦋0⦌) q))
  have hResult : V.app (op ⦋0⦌) (ComposableArrows.mk₀ (flag.{u} (1 : Fin 2))) = W.app (op ⦋0⦌) q :=
    (congrArg (fun p => V.app (op ⦋0⦌) p) hFlag).trans
      (hCell.trans ((congrArg (fun t => (eComp SSet.{u} x x y).app (op ⦋0⦌) (t, W.app (op ⦋0⦌) q))
        hPrefix).trans hUnit))
  have hR := MappingVertexOperators.read_operator x y (SimplexCategory.δ (0 : Fin 2)) σ
  exact (scalar_face η 0 1 rfl).trans (hE.trans (hResult.trans hR.symm))

/-- A genuine right-mapping-space edge determines an actual original Hom edge at precisely its same original
  endpoint vertices. -/
def readEdge {σ τ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋0⦌}
    (e : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)).Edge σ τ) :
    (x ⟶[SSet.{u}] y).Edge (MappingVertices.read x y σ) (MappingVertices.read x y τ) :=
  .mk (readSimplex x y e.edge)
    ((read_source x y e.edge).trans (congrArg (MappingVertices.read x y) e.src_eq))
    ((read_target x y e.edge).trans (congrArg (MappingVertices.read x y) e.tgt_eq))

/-- The actual original Hom component equality of a supplied mapping edge is derived from its literal readback edge. -/
theorem read_component_eq {σ τ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
    (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) _⦋0⦌}
    (e : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)).Edge σ τ) :
    SSet.π₀.mk (MappingVertices.read x y σ) = SSet.π₀.mk (MappingVertices.read x y τ) := SSet.π₀.sound (readEdge x y e)

end CategoryTheory.CoherentRealization.MappingComponentEdges
