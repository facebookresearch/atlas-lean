/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCartesianEndpointWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningCriticalLift
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrationCellLifting

/-!
# The SAME literal native unstraightening projection has Cartesian lifts

The actual original marked endpoint weak image gives every original
endpoint lift through the genuine native adjunction. The full native
terminal isomorphism retains the literal original total projection.
Together with the original inner and critical lifts, this proves its
genuine Cartesian fibration predicate for every coherent-model fibrant
diagram over arbitrary original bases. Exact Cartesian marking remains
a further intrinsic condition; no full St/Un model claim is inferred.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME actual original Cartesian endpoint is its exact original fixed-cell summand, with an unchanged
singleton index. -/
def nativeOriginalCartesianEndpoint (_ : Unit) : Arrow Marked.{u} := cartesianCell (.inr (.inr (0 : Fin 3)))

/-- The original endpoint family retains every supplied whole marked base edge. -/
def nativeOriginalCartesianEndpointsOver (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  overCells nativeOriginalCartesianEndpoint.{u} (max B)

/-- Every SAME whole original marked endpoint over its original complete base map has the actual native weak
projective image. -/
theorem nativeOriginalCartesianEndpointOverCell_straightening_projectiveWeakLeft (B : SSet.{u})
    (s : OverCellIndex nativeOriginalCartesianEndpoint.{u} (max B)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (overCell nativeOriginalCartesianEndpoint.{u} (max B) s)) :=
  nativeOriginalCartesianEndpointOver_straightening_projectiveWeakLeft B s.2

/-- Actual native Un of every genuine original coherent-model fibration retains all SAME original Cartesian endpoint
lifts over every whole original base map. -/
theorem nativeUnstraightening_map_originalCartesianEndpointRlp (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → (nativeOriginalCartesianEndpointsOver B).rlp ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let J := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos
  have hq' : J.rlp q := (fibration_iff q).mp hq
  rintro X Y i ⟨s⟩
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (overCell nativeOriginalCartesianEndpoint.{u} (max B) s) q).mp
      ((nativeOriginalCartesianEndpointOverCell_straightening_projectiveWeakLeft B s) q hq')

/-- The SAME LITERAL original native projection has the actual original marked target-endpoint lifting property for
every coherent-model fibrant diagram. -/
theorem nativeUnstraighteningProjection_originalCartesianEndpointLifting (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → HasLiftingProperty cartesianEndpointCell.{u} (nativeUnstraighteningProjection B F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let C := nativeOriginalCartesianEndpointsOver B
  let a := (nativeUnstraightening B).map (terminal.from F)
  let e := nativeUnstraighteningTerminalIso B
  have ha : C.rlp a := nativeUnstraightening_map_originalCartesianEndpointRlp B (terminal.from F) hF
  have hb : C.rlp e.hom := C.rlp_of_isIso e.hom
  have hc : C.rlp (a ≫ e.hom) := C.rlp.comp_mem _ _ ha hb
  have h : (ofHoms (fun s : Unit => (nativeOriginalCartesianEndpoint.{u} s).hom)).rlp (a ≫ e.hom).left :=
    (overCells_rlp_iff nativeOriginalCartesianEndpoint.{u} (max B) (a ≫ e.hom)).mp hc
  have hp : (a ≫ e.hom).left = nativeUnstraighteningProjection B F := nativeUnstraighteningTerminalIso_projection B F
  have h' : (ofHoms (fun s : Unit => (nativeOriginalCartesianEndpoint.{u} s).hom)).rlp
    (nativeUnstraighteningProjection B F) :=
    Eq.mp (congrArg (fun f => (ofHoms (fun s : Unit => (nativeOriginalCartesianEndpoint.{u} s).hom)).rlp f) hp) h
  exact h' _ (ofHoms.mk (f := fun s : Unit => (nativeOriginalCartesianEndpoint.{u} s).hom) ())

/-- The SAME literal native projection retains every original marked Cartesian edge lift and its whole prescribed
base edge and endpoint. -/
theorem nativeUnstraighteningProjection_originalMarkedLift (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ (a : (Δ[0] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
      (b : (Δ[1] : SSet.{u}) ⟶ B),
      a ≫ (nativeUnstraighteningProjection B F).hom = SSet.stdSimplex.δ (0 : Fin 2) ≫ b →
      ∃ f : max (Δ[1] : SSet.{u}) ⟶ nativeUnstraighteningTotal B F,
        SSet.stdSimplex.δ (0 : Fin 2) ≫ f.hom = a ∧
          f.hom ≫ (nativeUnstraighteningProjection B F).hom = b := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  exact (cartesianEndpointCell_rlp_iff (nativeUnstraighteningProjection B F)).mp
    (nativeUnstraighteningProjection_originalCartesianEndpointLifting B F hF)

/-- The SAME LITERAL ORIGINAL native projection is genuinely a Cartesian fibration for every coherent-model fibrant
diagram, over arbitrary original bases and without a Kan hypothesis. -/
theorem nativeUnstraighteningProjection_cartesianFibration (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → CartesianFibration (nativeUnstraighteningProjection B F).hom := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let p := nativeUnstraighteningProjection B F
  let _ : InnerFibration p.hom := nativeUnstraighteningProjection_innerFibration B F hF
  exact cartesianFibration_of_cell_lifting p ((innerCell_rlp_iff p).mpr inferInstance)
    (nativeUnstraighteningProjection_originalCartesianEndpointLifting B F hF)
    (nativeUnstraighteningProjection_originalCriticalLifting B F hF)

end SSet.Marked
