/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalMarkingPushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFreeNaturality

/-!
# The whole original critical interval charts and their exact cone and horn mates

The SAME original final edge indexes actual enriched left extensions
of the full minimal and sharp interval cones. Its whole direct-image
operators enter the entire original cone and horn, with the critical
marking on their sharp targets. The genuine universal maps retain both
complete marking squares; no chart identification is a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original critical edge indexes the actual opposite coherent interval inclusion. -/
def coneCriticalEdgeIndex (n : ℕ) :
    EnrichedFunctor SSet.{u} (Index.{u} 1)ᵒᵖ (Index.{u} (n + 2))ᵒᵖ :=
  EnrichedFunctor.opposite (indexMap (coneCriticalEdgeOrder n))

/-- Every original interval vertex maps to an actual positive original coefficient. -/
theorem coneCriticalEdgePositive (n : ℕ) (i : Vertex.{u} 1) :
    (⊥ : Vertex.{u} (n + 2)) < coneCriticalEdgeOrder n i :=
  (coneCriticalPrevious_pos.{u} n).trans_le ((coneCriticalEdgeOrder n).monotone (bot_le : (⊥ : Vertex.{u} 1) ≤ i))

/-- Each entire original sharp interval coefficient follows the SAME whole critical edge operator into its exact
critical marking. -/
def coneCriticalEdgeSharpWeight (n : ℕ) (i : Vertex.{u} 1) :
    max (coneWeight i).toSSet ⟶ coneCriticalWeight n (coneCriticalEdgeOrder n i) where
  hom := (coneImage (coneCriticalEdgeOrder n) i).hom
  preserve {e} _ := by
    change coneCriticalMaximumCollapse n ((e.obj 0).image (coneCriticalEdgeOrder n)).maximum =
      coneCriticalMaximumCollapse n ((e.obj 1).image (coneCriticalEdgeOrder n)).maximum
    rw [ConeSubset.image_maximum, ConeSubset.image_maximum]
    exact (coneCriticalEdgeOrder_collapsed n (e.obj 0).maximum).trans
      (coneCriticalEdgeOrder_collapsed n (e.obj 1).maximum).symm

/-- The full ORIGINAL sharp critical interval operator retains every original path and cone subset. -/
def coneCriticalEdgeSharpOperator (n : ℕ) :
    sharpConeDiagram 1 ⟶ (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).obj (coneCriticalDiagram.{u} n) where
  app i := coneCriticalEdgeSharpWeight n i.unop.as
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.image_prepend (coneCriticalEdgeOrder n) _ _

/-- The whole original minimal critical interval maps into the SAME full original supported terminal horn. -/
def coneCriticalEdgeMinimalHornOperator (n : ℕ) :
    coneDiagram 1 ⟶ (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).obj
      (coneRootHornDiagram.{u} (Fin.last (n + 2))) where
  app i := coneImage (coneCriticalEdgeOrder n) i.unop.as ≫
    (coneRootHornAboveIso (Fin.last (n + 2)) (coneCriticalEdgePositive n i.unop.as)).inv
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.image_prepend (coneCriticalEdgeOrder n) _ _

/-- The SAME whole sharp interval operator retains the full original critically marked terminal horn support. -/
def coneCriticalEdgeSharpHornOperator (n : ℕ) :
    sharpConeDiagram 1 ⟶ (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).obj
      (coneCriticalHornDiagram.{u} n) where
  app i := coneCriticalEdgeSharpWeight n i.unop.as ≫
    (coneCriticalHornAboveIso n (coneCriticalEdgePositive n i.unop.as)).inv
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    exact ConeSubset.image_prepend (coneCriticalEdgeOrder n) _ _

/-- The entire original interval and whole cone operator retain the SAME original critical marking square. -/
theorem coneCriticalEdgeSharpOperator_marking (n : ℕ) :
    coneSharp 1 ≫ coneCriticalEdgeSharpOperator n = coneOperator (coneCriticalEdgeOrder n) ≫
      (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).map (coneCriticalDiagramMark.{u} n) := by
  apply EnrichedDiagramMap.ext
  funext i
  exact Hom.ext rfl

/-- Both entire original terminal horn operators keep exactly the SAME original critical marking square. -/
theorem coneCriticalEdgeSharpHornOperator_marking (n : ℕ) :
    coneSharp 1 ≫ coneCriticalEdgeSharpHornOperator n = coneCriticalEdgeMinimalHornOperator n ≫
      (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).map (coneCriticalHornDiagramMark.{u} n) := by
  apply EnrichedDiagramMap.ext
  funext i
  exact Hom.ext rfl

/-- The full original minimal interval chart at the SAME actual critical edge. -/
def coneCriticalEdgeMinimalChart (n : ℕ) : EnrichedDiagram (Index.{u} (n + 2))ᵒᵖ :=
  EnrichedLeftKan.object (coneCriticalEdgeIndex n) (coneDiagram 1)

/-- The full original sharp interval chart at precisely that SAME original edge. -/
def coneCriticalEdgeSharpChart (n : ℕ) : EnrichedDiagram (Index.{u} (n + 2))ᵒᵖ :=
  EnrichedLeftKan.object (coneCriticalEdgeIndex n) (sharpConeDiagram 1)

/-- The entire original interval marking chart map is its actual enriched left extension. -/
def coneCriticalEdgeMarkingChartMap (n : ℕ) : coneCriticalEdgeMinimalChart.{u} n ⟶ coneCriticalEdgeSharpChart n :=
  (EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n)).map (coneSharp 1)

/-- The whole original minimal critical interval enters the original complete cone by its genuine universal mate. -/
def coneCriticalConeEdgeMap (n : ℕ) : coneCriticalEdgeMinimalChart.{u} n ⟶ coneDiagram (n + 2) :=
  (EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (coneDiagram 1) (coneDiagram (n + 2))).symm
    (coneOperator (coneCriticalEdgeOrder n))

/-- The SAME whole sharp edge enters the entire critically marked cone by its actual original universal mate. -/
def coneCriticalConeSharpEdgeMap (n : ℕ) : coneCriticalEdgeSharpChart.{u} n ⟶ coneCriticalDiagram n :=
  (EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (sharpConeDiagram 1) (coneCriticalDiagram n)).symm
    (coneCriticalEdgeSharpOperator n)

/-- The full original minimal critical interval enters the SAME complete original horn by its actual universal mate. -/
def coneCriticalHornEdgeMap (n : ℕ) :
    coneCriticalEdgeMinimalChart.{u} n ⟶ coneRootHornDiagram (Fin.last (n + 2)) :=
  (EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (coneDiagram 1)
    (coneRootHornDiagram (Fin.last (n + 2)))).symm (coneCriticalEdgeMinimalHornOperator n)

/-- The SAME whole sharp interval enters the entire original critically marked horn by its genuine original mate. -/
def coneCriticalHornSharpEdgeMap (n : ℕ) : coneCriticalEdgeSharpChart.{u} n ⟶ coneCriticalHornDiagram n :=
  (EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (sharpConeDiagram 1) (coneCriticalHornDiagram n)).symm
    (coneCriticalEdgeSharpHornOperator n)

/-- The original cone edge mate reads its exact whole original cone operator. -/
theorem coneCriticalConeEdgeMap_homEquiv (n : ℕ) :
    EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (coneDiagram 1) (coneDiagram (n + 2))
      (coneCriticalConeEdgeMap.{u} n) = coneOperator (coneCriticalEdgeOrder n) :=
  (EnrichedLeftKan.universalHomEquiv _ _ _).apply_symm_apply _

/-- The SAME whole sharp cone mate reads the genuine full critical operator. -/
theorem coneCriticalConeSharpEdgeMap_homEquiv (n : ℕ) :
    EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (sharpConeDiagram 1) (coneCriticalDiagram n)
      (coneCriticalConeSharpEdgeMap.{u} n) = coneCriticalEdgeSharpOperator n :=
  (EnrichedLeftKan.universalHomEquiv _ _ _).apply_symm_apply _

/-- The actual whole minimal horn mate retains its SAME complete original interval operator. -/
theorem coneCriticalHornEdgeMap_homEquiv (n : ℕ) :
    EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (coneDiagram 1)
      (coneRootHornDiagram (Fin.last (n + 2))) (coneCriticalHornEdgeMap.{u} n) =
        coneCriticalEdgeMinimalHornOperator n :=
  (EnrichedLeftKan.universalHomEquiv _ _ _).apply_symm_apply _

/-- The full sharp horn mate reads precisely its original critical interval operator. -/
theorem coneCriticalHornSharpEdgeMap_homEquiv (n : ℕ) :
    EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (sharpConeDiagram 1) (coneCriticalHornDiagram n)
      (coneCriticalHornSharpEdgeMap.{u} n) = coneCriticalEdgeSharpHornOperator n :=
  (EnrichedLeftKan.universalHomEquiv _ _ _).apply_symm_apply _

/-- The entire original interval chart and cone mates retain their SAME original marking square. -/
theorem coneCriticalConeEdgeMarking_condition (n : ℕ) :
    coneCriticalEdgeMarkingChartMap n ≫ coneCriticalConeSharpEdgeMap n =
      coneCriticalConeEdgeMap n ≫ coneCriticalDiagramMark.{u} n := by
  apply (EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (coneDiagram 1) (coneCriticalDiagram n)).injective
  have hl := enrichedLeftKan_universal_map_post (coneCriticalEdgeIndex n) (coneSharp 1) (coneCriticalConeSharpEdgeMap n)
  have hr := EnrichedLeftKan.universalHomEquiv_natural_right (coneCriticalEdgeIndex n) (coneDiagram 1)
    (coneCriticalConeEdgeMap n) (coneCriticalDiagramMark n)
  rw [coneCriticalConeSharpEdgeMap_homEquiv] at hl
  rw [coneCriticalConeEdgeMap_homEquiv] at hr
  exact hl.trans ((coneCriticalEdgeSharpOperator_marking n).trans hr.symm)

/-- The SAME full original interval marking chart square retains the entire critically marked terminal horn. -/
theorem coneCriticalHornEdgeMarking_condition (n : ℕ) :
    coneCriticalEdgeMarkingChartMap n ≫ coneCriticalHornSharpEdgeMap n =
      coneCriticalHornEdgeMap n ≫ coneCriticalHornDiagramMark.{u} n := by
  apply (EnrichedLeftKan.universalHomEquiv (coneCriticalEdgeIndex n) (coneDiagram 1) (coneCriticalHornDiagram
    n)).injective
  have hl := enrichedLeftKan_universal_map_post (coneCriticalEdgeIndex n) (coneSharp 1) (coneCriticalHornSharpEdgeMap n)
  have hr := EnrichedLeftKan.universalHomEquiv_natural_right (coneCriticalEdgeIndex n) (coneDiagram 1)
    (coneCriticalHornEdgeMap n) (coneCriticalHornDiagramMark n)
  rw [coneCriticalHornSharpEdgeMap_homEquiv] at hl
  rw [coneCriticalHornEdgeMap_homEquiv] at hr
  exact hl.trans ((coneCriticalEdgeSharpHornOperator_marking n).trans hr.symm)

end SSet.Marked.CoherentWeight
