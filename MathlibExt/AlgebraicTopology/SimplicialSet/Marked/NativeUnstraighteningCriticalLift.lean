/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCriticalStraightening
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningInnerProjection
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalRLP

/-!
# The literal native unstraightening projection has original critical lifts

The actual coherent terminal map and its genuine native terminal
isomorphism retain the original marked total projection. The same
original critical-cell right lifts therefore apply to this literal
projection for every genuine coherent-model fibrant diagram. The full
original relative horn criterion proves every supplied marked edge is
Cartesian. Cartesian edge existence and exact marking remain further
intrinsic conditions; they are not inferred from these critical lifts.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME literal original native projection lifts every full original critically marked horn cell, over
arbitrary original bases. -/
theorem nativeUnstraighteningProjection_originalCriticalLifting (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ n : ℕ, HasLiftingProperty (cartesianCriticalCell.{u} n) (nativeUnstraighteningProjection B F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let C := nativeOriginalCriticalCellsOver B
  let a := (nativeUnstraightening B).map (terminal.from F)
  let e := nativeUnstraighteningTerminalIso B
  have ha : C.rlp a := nativeUnstraightening_map_originalCriticalRlp B (terminal.from F) hF
  have hb : C.rlp e.hom := C.rlp_of_isIso e.hom
  have hc : C.rlp (a ≫ e.hom) := C.rlp.comp_mem _ _ ha hb
  have h : (ofHoms (fun n : ℕ => (nativeOriginalCriticalCell.{u} n).hom)).rlp (a ≫ e.hom).left :=
    (overCells_rlp_iff nativeOriginalCriticalCell.{u} (max B) (a ≫ e.hom)).mp hc
  have hp : (a ≫ e.hom).left = nativeUnstraighteningProjection B F :=
    nativeUnstraighteningTerminalIso_projection B F
  have h' : (ofHoms (fun n : ℕ => (nativeOriginalCriticalCell.{u} n).hom)).rlp (nativeUnstraighteningProjection B F) :=
    Eq.mp (congrArg (fun f => (ofHoms (fun n : ℕ => (nativeOriginalCriticalCell.{u} n).hom)).rlp f) hp) h
  intro n
  exact h' _ (ofHoms.mk (f := fun n : ℕ => (nativeOriginalCriticalCell.{u} n).hom) n)

/-- Every SAME original marked edge of the literal native total projection is genuinely Cartesian for a
coherent-model fibrant diagram, with its entire original relative horn and base map retained. -/
theorem nativeUnstraighteningProjection_marked_cartesian (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ e : (nativeUnstraighteningTotal B F).toSSet _⦋1⦌,
      e ∈ (nativeUnstraighteningTotal B F).marking →
        CartesianEdge.IsPCartesian (nativeUnstraighteningProjection B F).hom (SSet.yonedaEquiv.symm e) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  exact (cartesianCriticalCell_rlp_iff (nativeUnstraighteningProjection B F)).mp
    (nativeUnstraighteningProjection_originalCriticalLifting B F hF)

end SSet.Marked
