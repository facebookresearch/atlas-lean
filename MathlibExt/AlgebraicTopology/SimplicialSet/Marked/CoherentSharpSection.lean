/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentSharpCone
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOneEdges

/-!
# The actual sharp one-simplex cone section criterion

A full marked section of the maximum-preserving cone extends to the
sharp cone precisely when its original coefficient edge is marked.
Every original cone edge is covered by the proved finite edge
classification. Both directions retain the same entire underlying
simplicial section and whole enriched naturality.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable (F : EnrichedDiagram (Index.{u} 1)ᵒᵖ)

/-- The original cone section extends to the sharp weight exactly on its actual marked coefficient edge. -/
def sharpenSection (a : coneDiagram 1 ⟶ F)
    (h : (a.app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌) coefficientEdge ∈
      (F.obj (op (SimplicialThickening.mk zeroOne))).marking) : sharpConeDiagram 1 ⟶ F where
  app i :=
    { hom := (a.app i).hom
      preserve {e} _ := by
        cases i with
        | op i =>
          cases i with
          | mk i =>
            cases i with
            | up i =>
              fin_cases i
              · rcases coneWeight_zeroOne_edge e with he | he
                · exact (a.app _).preserve he
                · exact he ▸ h
              · exact (a.app _).preserve (coneWeight_one_marked e) }
  naturality i j := by
    ext n f
    apply Hom.ext
    have h := congr($(a.naturality i j).app n f)
    exact congrArg
      (fun m : (mappingComplex .maximal ((coneDiagram 1).obj i) (F.obj j)).obj n => m.hom) h

/-- The original cone map into its sharpened section is exactly the same full original section. -/
theorem coneSharp_sharpenSection (a : coneDiagram 1 ⟶ F)
    (h : (a.app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌) coefficientEdge ∈
      (F.obj (op (SimplicialThickening.mk zeroOne))).marking) :
    coneSharp 1 ≫ sharpenSection F a h = a := by
  apply EnrichedDiagramMap.ext
  funext i
  apply Hom.ext
  rfl

/-- An actual sharp cone section marks precisely the original coefficient edge of its restricted section. -/
theorem sharpSection_coefficient_marked (a : sharpConeDiagram 1 ⟶ F) :
    ((coneSharp 1 ≫ a).app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌) coefficientEdge ∈
      (F.obj (op (SimplicialThickening.mk zeroOne))).marking :=
  (a.app (op (SimplicialThickening.mk zeroOne))).preserve (Set.mem_univ _)

/-- Sharpening the restricted original data recovers every entire original sharp section component. -/
theorem sharpenSection_coneSharp (a : sharpConeDiagram 1 ⟶ F) :
    sharpenSection F (coneSharp 1 ≫ a) (sharpSection_coefficient_marked F a) = a := by
  apply EnrichedDiagramMap.ext
  funext i
  apply Hom.ext
  rfl

/-- Whole sharp-cone maps correspond to exactly the original marked coefficient-edge condition. -/
def sharpSectionEquiv :
    (sharpConeDiagram 1 ⟶ F) ≃
      {a : coneDiagram 1 ⟶ F //
        (a.app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌) coefficientEdge ∈
          (F.obj (op (SimplicialThickening.mk zeroOne))).marking} where
  toFun a := ⟨coneSharp 1 ≫ a, sharpSection_coefficient_marked F a⟩
  invFun a := sharpenSection F a.val a.property
  left_inv := sharpenSection_coneSharp F
  right_inv a := Subtype.ext (coneSharp_sharpenSection F a.val a.property)

end SSet.Marked.CoherentWeight
