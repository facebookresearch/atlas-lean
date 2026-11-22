/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalAction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# The same whole original cone with its genuine critical marked enrichment

Every original path-union action preserves the actual critical last-edge
coefficient marking. The original singleton and full union composition
laws give its genuine marked enriched diagram. The same underlying
identity marks the original cone, and the exact original final-degeneracy
operator retains a whole enriched projection to its restricted target.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The SAME whole original cone coefficients and paths form their genuine marked enriched diagram with the exact
original critical last-edge marking. -/
def coneCriticalDiagram (n : ℕ) : EnrichedDiagram (Index.{u} (n + 2))ᵒᵖ where
  obj i := coneCriticalWeight n i.unop.as
  map i j := maxCurry (coneCriticalAction n j.unop.as i.unop.as)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.prepend_id _
  map_comp i j k := by
    ext q fg
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact (ConeSubset.prepend_comp _ _ _).symm

/-- Every entire original critical enriched action is precisely its same original full marked path-union map. -/
theorem coneCriticalDiagram_action (n : ℕ) (i j : Index.{u} (n + 2)) :
    enrichedDiagramAction (coneCriticalDiagram n) (op j) (op i) = coneCriticalAction n i.as j.as :=
      maxUncurry_maxCurry _

/-- The complete original constant-maximum cone enters the SAME critical marking by its literal whole enriched
component identities. -/
def coneCriticalDiagramMark (n : ℕ) : coneDiagram (n + 2) ⟶ coneCriticalDiagram.{u} n where
  app i := coneCriticalMark n i.unop.as
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    rfl

/-- The SAME complete original critical diagram projects through the actual original whole final-degeneracy
operator, with every original path and scalar map retained. -/
def coneCriticalDiagramProjection (n : ℕ) :
    coneCriticalDiagram.{u} n ⟶ coneRestricted (coneCriticalMaximumCollapse n) where
  app i := coneCriticalProjection n i.unop.as
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.image_prepend (coneCriticalMaximumCollapse n) _ _

/-- The whole original critical marking and genuine enriched projection retain exactly the original full
final-degeneracy cone operator. -/
theorem coneCriticalDiagramMark_projection (n : ℕ) :
    coneCriticalDiagramMark.{u} n ≫ coneCriticalDiagramProjection n = coneOperator (coneCriticalMaximumCollapse n) := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneCriticalMark_projection n i.unop.as

end SSet.Marked.CoherentWeight
