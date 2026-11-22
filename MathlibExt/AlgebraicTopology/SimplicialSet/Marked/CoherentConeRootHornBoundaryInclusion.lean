/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryPushout

/-!
# The SAME original supported horn inside the complete original root boundary

Every original horn coordinate is an original boundary coordinate. Above
root both supports retain the same whole original cone coefficient. The
literal support inclusions preserve the complete inherited marking and
original path actions, giving the full original enriched inclusion and
its unchanged full-cone attaching square.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Every SAME original upper and eligible lower horn coordinate is an original full root-boundary coordinate. -/
theorem coneRootCoordinateHorn_le_boundary {n : ℕ} (k : Fin (n + 2)) :
    coneRootCoordinateHorn.{u} k ≤ coneCoordinateBoundary (⊥ : Vertex.{u} (n + 1)) := by
  intro q a ha
  apply (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} (n + 1)) a).mpr
  rcases (mem_coneRootCoordinateHorn_iff k q a).mp ha with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, true, fun t => ⟨fun _ => rfl, fun _ => hc t⟩⟩
  · refine ⟨⟨c.val, c.property.1⟩, false, fun t => ?_⟩
    constructor
    · intro h
      exact (hc t h).elim
    · intro h
      cases h

/-- Each original horn support enters the SAME original root-boundary support, retaining whole positive coefficients. -/
theorem coneRootHornSupport_le_boundary {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    coneRootHornSupport k i ≤ coneRootBoundarySupport i := by
  intro q a ha
  by_cases hi : i = ⊥
  · subst i
    have hh := (congrArg (fun A => a ∈ A.obj q) (coneRootHornSupport_root k)).to_iff.mp ha
    exact (congrArg (fun A => a ∈ A.obj q) (coneRootBoundarySupport_root (n + 1))).to_iff.mpr
      (coneRootCoordinateHorn_le_boundary k q hh)
  · have hpos : (⊥ : Vertex.{u} (n + 1)) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
    exact (congrArg (fun A => a ∈ A.obj q) (coneRootBoundarySupport_above hpos)).to_iff.mpr (Set.mem_univ _)

/-- The SAME original marked horn coefficient enters its complete original marked root boundary by its literal
support inclusion. -/
def coneRootHornToBoundary {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    coneRootHornMarked k i ⟶ coneRootBoundaryMarked i where
  hom := Subcomplex.homOfLE (coneRootHornSupport_le_boundary k i)
  preserve he := he

/-- The actual whole original supported horn-to-boundary coefficient map is monic on its unchanged carrier. -/
instance {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) : Mono (coneRootHornToBoundary k i) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (Subcomplex.homOfLE (coneRootHornSupport_le_boundary k i)))

/-- Every literal original coefficient support inclusion retains its SAME entire original full-cone attaching map. -/
theorem coneRootHornToBoundary_inclusion {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    coneRootHornToBoundary k i ≫ coneRootBoundaryInclusion i = coneRootHornInclusion k i :=
  Hom.ext (Subcomplex.homOfLE_ι (coneRootHornSupport_le_boundary k i))

/-- Above root the SAME original supported horn and boundary are the actual whole original coefficient isomorphism. -/
def coneRootHornToBoundaryAboveIso {n : ℕ} (k : Fin (n + 2)) {i : Vertex.{u} (n + 1)}
    (hi : (⊥ : Vertex.{u} (n + 1)) < i) : coneRootHornMarked k i ≅ coneRootBoundaryMarked i :=
  coneRootHornAboveIso k hi ≪≫ (coneRootBoundaryAboveIso hi).symm

/-- The original positive-coefficient isomorphism retains precisely the literal original support inclusion. -/
theorem coneRootHornToBoundaryAboveIso_hom {n : ℕ} (k : Fin (n + 2)) {i : Vertex.{u} (n + 1)}
    (hi : (⊥ : Vertex.{u} (n + 1)) < i) : (coneRootHornToBoundaryAboveIso k hi).hom = coneRootHornToBoundary k i :=
  Hom.ext rfl

/-- The SAME original whole marked enriched horn diagram enters its complete original root-boundary diagram through
all literal original support inclusions and unchanged path actions. -/
def coneRootHornToBoundaryDiagramMap {n : ℕ} (k : Fin (n + 2)) :
    coneRootHornDiagram.{u} k ⟶ coneRootBoundaryDiagram (n + 1) where
  app i := coneRootHornToBoundary k i.unop.as
  naturality i j := by
    ext q p
    apply Hom.ext
    ext r a
    rfl

/-- The entire original enriched support inclusion retains the SAME full original cone attaching square. -/
theorem coneRootHornToBoundaryDiagramMap_inclusion {n : ℕ} (k : Fin (n + 2)) :
    coneRootHornToBoundaryDiagramMap.{u} k ≫ coneRootBoundaryDiagramInclusion (n + 1) =
      coneRootHornDiagramInclusion k := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneRootHornToBoundary_inclusion k i.unop.as

end SSet.Marked.CoherentWeight
