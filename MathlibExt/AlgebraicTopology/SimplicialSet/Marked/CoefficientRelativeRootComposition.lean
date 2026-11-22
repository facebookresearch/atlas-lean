/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentRootTriangleCompositionWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramModel

/-!
# Actual coefficient fibrations reflect the original relative root composition

The same two-root-triangle marking cell is an actual coefficient trivial
cofibration. Its original source map keeps the entire supplied cone map,
and its original target map is that whole map followed by the actual
coefficient fibration. The genuine model lifting property marks the
original direct edge in the source without requiring either coefficient
to be fibrant. Actual projective fibrations retain this property at every
original coefficient object.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] vertexDecidableEq markedSimplicialCategory enrichedDiagramCategory
  coefficientMarkedModelCategory

/-- Every actual original projective fibration evaluates to an actual coefficient fibration, with neither diagram
assumed fibrant. -/
theorem coherentDiagramCoefficient_map_fibration (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (c : (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    Fibration q → Fibration (q.app c) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  have h := (fibration_iff q).mp hq
  rw [coherentDiagramModel_fibrations B] at h
  exact (fibration_iff _).mpr ((EvaluationTransfer.evaluationProperty_iff _ _ _).mp h c)

/-- An actual coefficient fibration reflects the same original direct-edge mark when the original first and middle
edges and its target direct edge are marked. -/
theorem coefficientFibration_rootTriangle_direct_marked {A D : Marked.{u}} (q : A ⟶ D)
    (hq : Fibration q) (g : coneWeight rootTriangleZero.{u} ⟶ A)
    (hfirst : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ A.marking)
    (hmiddle : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈ A.marking)
    (hdirect : (g ≫ q).hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ D.marking) :
    g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ A.marking := by
  let t : rootTriangleCompositionSource.{u} ⟶ A :=
    { hom := g.hom
      preserve {e} he := by
        rcases he with ho | hf | hm
        · exact g.preserve ho
        · exact hf ▸ hfirst
        · exact hm ▸ hmiddle }
  let b : rootTriangleCompositionTarget.{u} ⟶ D :=
    { hom := g.hom ≫ q.hom
      preserve {e} he := by
        rcases he with hs | hd
        · exact q.preserve (t.preserve hs)
        · exact hd ▸ hdirect }
  have hcell : (fibrations Marked.{u}).llp rootTriangleCompositionCell.{u} := by
    rw [fibrations_llp]
    exact rootTriangleCompositionCell_trivialCofibration
  have hlp : HasLiftingProperty rootTriangleCompositionCell.{u} q :=
    hcell q ((fibration_iff q).mp hq)
  let sq : CommSq t rootTriangleCompositionCell.{u} q b :=
    ⟨Hom.ext (Category.id_comp _).symm⟩
  obtain ⟨l, hl, _⟩ := hlp.sq_hasLift sq
  have hwhole : l.hom = g.hom := (Category.id_comp l.hom).symm.trans (congrArg Hom.hom hl)
  exact hwhole ▸ l.preserve rootTriangleComposition_direct_marked

/-- The original direct mark follows at every actual coefficient of a coherent-model fibration from the same two
whole root triangles. -/
theorem coherentDiagramCoefficient_relative_rootComposition (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (c : (realization B)ᵒᵖ)
    (g : coneWeight rootTriangleZero.{u} ⟶ F.obj c)
    (hfirst : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ (F.obj c).marking)
    (hmiddle : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈ (F.obj c).marking)
    (hdirect : (g ≫ q.app c).hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ (G.obj c).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ (F.obj c).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  exact coefficientFibration_rootTriangle_direct_marked (q.app c)
    (coherentDiagramCoefficient_map_fibration B q c hq) g hfirst hmiddle hdirect

end SSet.Marked
