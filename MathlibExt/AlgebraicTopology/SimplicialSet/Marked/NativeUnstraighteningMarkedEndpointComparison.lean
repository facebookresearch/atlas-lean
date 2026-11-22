/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointMarkingCorners
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.BoundaryCells

/-!
# The actual original marked endpoint comparison is mono-right

The original minimally marked boundary corners and original edge-mark
corner lift the same native map of every actual coherent-model
fibration. The existing marked product/internal-Hom adjunction transfers
them to the same actual marked pullback comparison. The exact original
marked mono-generator recognition then proves all marked-mono lifting,
retaining the original endpoint, whole parameter and marked target map.
Neither diagram nor base is required to be fibrant, Kan or a quasicategory.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same original marked internal-Hom endpoint comparison of an actual native model-fibration map lifts every
original marked monomorphism. -/
theorem nativeUnstraightening_markedEndpointComparison_monoRight (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → (monomorphisms Marked.{u}).rlp
      (markedInternalHomComparison cartesianEndpointCell.{u} ((nativeUnstraightening B).map q).left) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p := ((nativeUnstraightening B).map q).left
  let c := markedInternalHomComparison cartesianEndpointCell.{u} p
  apply (monoCells_rlp_iff c).mp
  rintro X Y i ⟨s⟩
  rcases s with n | s
  · exact (markedPushoutProduct_hasLiftingProperty_iff cartesianEndpointCell.{u} (boundaryCell.{u} n) p).mp
      (nativeUnstraightening_map_endpointMinimalBoundaryCornerLifting B q n hq)
  · cases s
    exact (markedPushoutProduct_hasLiftingProperty_iff cartesianEndpointCell.{u} edgeMarkCell.{u} p).mp
      (nativeUnstraightening_map_endpointMarkingCornerLifting B q hq)

/-- Every same original marked-mono parameter endpoint corner retains its full native lift through the actual
original product adjunction and mono comparison. -/
theorem nativeUnstraightening_map_markedEndpointMonoCornerLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ {A D : Marked.{u}} (a : A ⟶ D), Mono a →
      HasLiftingProperty (markedPushoutProduct cartesianEndpointCell.{u} a) ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq A D a ha
  exact (markedPushoutProduct_hasLiftingProperty_iff cartesianEndpointCell.{u} a ((nativeUnstraightening B).map
    q).left).mpr
    (nativeUnstraightening_markedEndpointComparison_monoRight B q hq a ha)

end SSet.Marked
