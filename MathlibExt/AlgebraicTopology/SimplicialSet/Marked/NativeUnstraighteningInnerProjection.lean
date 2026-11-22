/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalInnerHornStraightening
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The actual native unstraightening projection is an inner fibration

The genuine native adjunction identifies its image of the actual
coherent-model terminal object with the original terminal object of
the same marked slice. The original over equation retains the literal
native total-space projection. Original inner-cell lifts therefore prove
that this same projection is an inner fibration for every actual fibrant
coherent diagram. Over an original quasicategory, its unchanged entire
native total space is consequently a quasicategory.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same actual native right adjoint sends the original coherent-model terminal object to a genuine terminal
object in the unchanged original marked slice. -/
def nativeUnstraighteningTerminalIsTerminal (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    IsTerminal ((nativeUnstraightening B).obj (⊤_ (EnrichedDiagram (realization B)ᵒᵖ))) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  let R := nativeUnstraightening B
  let _ : PreservesLimitsOfSize.{0, 0} R := (nativeStraighteningAdjunction B).rightAdjoint_preservesLimits
  exact terminalIsTerminal.isTerminalObj R _

/-- The actual native image of the original coherent-model terminal object is isomorphic to the original marked
identity projection, preserving the full original slice records. -/
def nativeUnstraighteningTerminalIso (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    (nativeUnstraightening B).obj (⊤_ (EnrichedDiagram (realization B)ᵒᵖ)) ≅ Over.mk (𝟙 (max B)) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  exact (nativeUnstraighteningTerminalIsTerminal B).uniqueUpToIso Over.mkIdTerminal

/-- The original whole native over equation identifies the terminal-image composite with precisely the unchanged
actual native projection. -/
theorem nativeUnstraighteningTerminalIso_projection (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    ((nativeUnstraightening B).map (terminal.from F)).left ≫ (nativeUnstraighteningTerminalIso B).hom.left =
      nativeUnstraighteningProjection B F := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  exact (Category.comp_id _).symm.trans
    (Over.w ((nativeUnstraightening B).map (terminal.from F) ≫ (nativeUnstraighteningTerminalIso B).hom))

/-- The SAME entire original native marked projection is an actual underlying inner fibration for every genuine
fibrant object of the original coherent model, over arbitrary original simplicial bases. -/
theorem nativeUnstraighteningProjection_innerFibration (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → InnerFibration (nativeUnstraighteningProjection B F).hom := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let e := nativeUnstraighteningTerminalIso B
  let a := ((nativeUnstraightening B).map (terminal.from F)).left
  let b := e.hom.left
  have ha : InnerFibration a.hom := nativeUnstraightening_map_innerFibration B (terminal.from F) hF
  let _ : IsIso b.hom := (forget.mapIso ((Over.forget (max B)).mapIso e)).isIso_hom
  have hb : innerFibrations b.hom := innerHornInclusions.rlp_of_isIso b.hom
  have hp : a.hom ≫ b.hom = (nativeUnstraighteningProjection B F).hom :=
    congrArg Hom.hom (nativeUnstraighteningTerminalIso_projection B F)
  have h : innerFibrations (a.hom ≫ b.hom) := innerFibrations.comp_mem _ _ ha.mem hb
  exact ⟨Eq.mp (congrArg (fun f => innerFibrations f) hp) h⟩

/-- Over every original quasicategory, including non-Kan bases, the same entire native unstraightening total space
of a genuine coherent-model fibrant diagram is itself a quasicategory. -/
theorem nativeUnstraighteningTotal_quasicategory (B : SSet.{u}) [Quasicategory B]
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → Quasicategory (nativeUnstraighteningTotal B F).toSSet := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let _ : InnerFibration (nativeUnstraighteningProjection B F).hom :=
    nativeUnstraighteningProjection_innerFibration B F hF
  let _ : Quasicategory (max B).toSSet := (inferInstance : Quasicategory B)
  exact quasicategory_of_innerFibration (nativeUnstraighteningProjection B F).hom

end SSet.Marked
