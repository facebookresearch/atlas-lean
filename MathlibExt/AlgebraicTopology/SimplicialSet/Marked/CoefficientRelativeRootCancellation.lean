/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentRootTriangleCancellationWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientRelativeRootComposition

/-!
# Actual coefficient fibrations reflect original relative root cancellation

The same original root coefficient, direct and middle edges and
constant-maximum mark give an actual coefficient trivial cofibration
that adds the first-edge mark. Its genuine lift against each actual
coefficient fibration keeps the whole original root map. Neither
coefficient nor diagram is assumed fibrant.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] vertexDecidableEq markedSimplicialCategory enrichedDiagramCategory
  coefficientMarkedModelCategory

/-- An actual coefficient fibration reflects the same original first-edge mark from its marked target image, marked
direct edge and marked middle edge. -/
theorem coefficientFibration_rootTriangle_first_marked {A D : Marked.{u}} (q : A ⟶ D)
    (hq : Fibration q) (g : coneWeight rootTriangleZero.{u} ⟶ A)
    (hdirect : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ A.marking)
    (hmiddle : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈ A.marking)
    (hfirst : (g ≫ q).hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ D.marking) :
    g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ A.marking := by
  let t : rootTriangleCancellationSource.{u} ⟶ A :=
    { hom := g.hom
      preserve {e} he := by
        rcases he with ho | hd | hm
        · exact g.preserve ho
        · exact hd ▸ hdirect
        · exact hm ▸ hmiddle }
  let b : rootTriangleCancellationTarget.{u} ⟶ D :=
    { hom := g.hom ≫ q.hom
      preserve {e} he := by
        rcases he with hs | hf
        · exact q.preserve (t.preserve hs)
        · exact hf ▸ hfirst }
  have hcell : (fibrations Marked.{u}).llp rootTriangleCancellationCell.{u} := by
    rw [fibrations_llp]
    exact rootTriangleCancellationCell_trivialCofibration
  have hlp : HasLiftingProperty rootTriangleCancellationCell.{u} q := hcell q ((fibration_iff q).mp hq)
  let sq : CommSq t rootTriangleCancellationCell.{u} q b := ⟨Hom.ext (Category.id_comp _).symm⟩
  obtain ⟨l, hl, _⟩ := hlp.sq_hasLift sq
  have hwhole : l.hom = g.hom := (Category.id_comp l.hom).symm.trans (congrArg Hom.hom hl)
  exact hwhole ▸ l.preserve rootTriangleCancellation_first_marked

/-- Every original coefficient of an actual coherent-model fibration retains the whole original relative
cancellation and marked first edge. -/
theorem coherentDiagramCoefficient_relative_rootCancellation (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (c : (realization B)ᵒᵖ)
    (g : coneWeight rootTriangleZero.{u} ⟶ F.obj c)
    (hdirect : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ (F.obj c).marking)
    (hmiddle : g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈ (F.obj c).marking)
    (hfirst : (g ≫ q.app c).hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ (G.obj c).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → g.hom.app (op ⦋1⦌) (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ (F.obj c).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  exact coefficientFibration_rootTriangle_first_marked (q.app c)
    (coherentDiagramCoefficient_map_fibration B q c hq) g hdirect hmiddle hfirst

end SSet.Marked
