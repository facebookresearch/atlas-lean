/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningCartesianExistence
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PullbackMarkingCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CompositionCell

/-!
# The SAME native unstraightening marking preserves original composition

The original marked pullback marking is detected on its original two
projections through the actual sharp-interval universal property. The
maximally marked base imposes no additional edge condition. The whole
original coherent two-simplex composition proof therefore gives actual
composition-cell lifts for the SAME literal original native projection,
with every original base map and parameter retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME original native total edge is marked exactly when its whole original coherent coordinate edge is marked. -/
theorem nativeUnstraightening_marking_coherent_iff (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) (e : (nativeUnstraighteningTotal B F).toSSet _⦋1⦌) :
    e ∈ (nativeUnstraighteningTotal B F).marking ↔
      (nativeUnstraighteningCoherentProjection B F).hom.app (op ⦋1⦌) e ∈
        (coherentUnstraightening (realization B) F).marking := by
  exact (pullback_marking_iff (coherentUnstraighteningProjection (realization B) F)
    (maximal.map (unit B)) e).trans ⟨fun h => h.1, fun h => ⟨h, Set.mem_univ _⟩⟩

/-- The SAME literal original native projection has genuine original composition-cell lifting for every actual
coherent-model fibrant diagram over arbitrary original bases. -/
theorem nativeUnstraighteningProjection_compositionLifting (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → HasLiftingProperty compositionCell.{u} (nativeUnstraighteningProjection B F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  apply (compositionCell_rlp_iff (nativeUnstraighteningProjection B F)).mpr
  intro t h₂ h₀
  have h₂' := (nativeUnstraightening_marking_coherent_iff B F _).mp h₂
  have h₀' := (nativeUnstraightening_marking_coherent_iff B F _).mp h₀
  apply (nativeUnstraightening_marking_coherent_iff B F _).mpr
  exact coherentUnstraightening_composition_map B F hF
    (t ≫ (nativeUnstraighteningCoherentProjection B F).hom) h₂' h₀'

end SSet.Marked
