/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramAction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductSymmetry
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Whole Hom actions on actual marked pointwise colimits

The value at each original object is the genuine marked colimit of the
evaluated diagram. Its Hom action descends the original marked actions
because the native product is a left adjoint and preserves that
colimit. The full original injection equations expose the descended
map. This uses categorical colimits, not a functor-model outcome.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)

/-- The original marked values of the diagram at the specified source object. -/
abbrev evaluated (x : C) : J ⥤ Marked.{u} := K ⋙ enrichedDiagramEvaluation C x

/-- The actual Hom-action cocone retains the original component action followed by the value injection. -/
def actionCocone (x y : C) [HasColimit (evaluated K y)] :
    Cocone (evaluated K x ⋙ prodLeft (max (x ⟶[SSet.{u}] y))) where
  pt := colimit (evaluated K y)
  ι :=
    { app j := enrichedDiagramAction (K.obj j) x y ≫ colimit.ι (evaluated K y) j
      naturality i j f := by
        let ii : (K.obj i).obj y ⟶ colimit (evaluated K y) := colimit.ι (evaluated K y) i
        let ij : (K.obj j).obj y ⟶ colimit (evaluated K y) := colimit.ι (evaluated K y) j
        have hf : (K.map f).app y ≫ ij = ii := colimit.w (evaluated K y) f
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ ij) (enrichedDiagramAction_natural (K.map f) x y).symm).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun t => enrichedDiagramAction (K.obj i) x y ≫ t) hf).trans
                (Category.comp_id (enrichedDiagramAction (K.obj i) x y ≫ ii)).symm))) }

/-- The actual marked Hom action descends through the original evaluated colimit. -/
def action (x y : C) [HasColimit (evaluated K x)] [HasColimit (evaluated K y)] :
    prod (max (x ⟶[SSet.{u}] y)) (colimit (evaluated K x)) ⟶ colimit (evaluated K y) := by
  let _ : PreservesColimitsOfSize.{t, w} (prodLeft (max (x ⟶[SSet.{u}] y))) :=
    (leftProductAdjunction (max (x ⟶[SSet.{u}] y))).leftAdjoint_preservesColimits
  exact (isColimitOfPreserves (prodLeft (max (x ⟶[SSet.{u}] y)))
    (colimit.isColimit (evaluated K x))).desc (actionCocone K x y)

/-- Each whole original marked value injection commutes with the descended Hom action. -/
theorem injection_action (x y : C) [HasColimit (evaluated K x)] [HasColimit (evaluated K y)]
    (j : J) :
    prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (colimit.ι (evaluated K x) j) ≫ action K x y =
      enrichedDiagramAction (K.obj j) x y ≫ colimit.ι (evaluated K y) j := by
  let _ : PreservesColimitsOfSize.{t, w} (prodLeft (max (x ⟶[SSet.{u}] y))) :=
    (leftProductAdjunction (max (x ⟶[SSet.{u}] y))).leftAdjoint_preservesColimits
  exact (isColimitOfPreserves (prodLeft (max (x ⟶[SSet.{u}] y)))
    (colimit.isColimit (evaluated K x))).fac (actionCocone K x y) j

/-- The entire original enriched Hom map of an injection is the same curried action equation. -/
theorem injection_fullMap (x y : C) [HasColimit (evaluated K x)] [HasColimit (evaluated K y)]
    (j : J) :
    (K.obj j).map x y ≫ mappingComplexPost .maximal ((K.obj j).obj x)
        (colimit.ι (evaluated K y) j) =
      maxCurry (action K x y) ≫ mappingComplexPre .maximal
        (colimit.ι (evaluated K x) j) (colimit (evaluated K y)) := by
  let ix : (K.obj j).obj x ⟶ colimit (evaluated K x) := colimit.ι (evaluated K x) j
  let iy : (K.obj j).obj y ⟶ colimit (evaluated K y) := colimit.ι (evaluated K y) j
  have h := congrArg maxCurry (injection_action K x y j)
  have hs := maxCurry_source ix (action K x y)
  have ht := maxCurry_post (enrichedDiagramAction (K.obj j) x y) iy
  have hc : maxCurry (enrichedDiagramAction (K.obj j) x y) = (K.obj j).map x y :=
    maxCurry_maxUncurry _
  exact (hs.symm.trans
    (h.trans (ht.trans (congrArg (fun t => t ≫ mappingComplexPost .maximal ((K.obj j).obj x) iy) hc)))).symm

end SSet.Marked.EnrichedColimit
