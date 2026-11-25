/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitComposition

/-!
# Actual marked pointwise colimit objects and their whole enriched injections

The pointwise marked colimits have the proved original full Hom action,
identity and composition laws. Their injections preserve whole marked
prisms and form the actual original cocone, with independent indexing
and coefficient universes.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)
    [∀ x : C, HasColimit (evaluated K x)]

/-- The original pointwise marked colimits form a genuine enriched diagram with its full descended action. -/
def object : EnrichedDiagram C where
  obj x := colimit (evaluated K x)
  map x y := maxCurry (action K x y)
  map_id x := fullMap_id K x
  map_comp x y z := fullMap_comp K x y z

/-- Each actual marked value injection is a whole enriched natural map. -/
def injection (j : J) : K.obj j ⟶ object K where
  app x := colimit.ι (evaluated K x) j
  naturality x y := injection_fullMap K x y j

/-- Original enriched injection components are precisely the native marked colimit injections. -/
theorem injection_app (j : J) (x : C) :
    (injection K j).app x = colimit.ι (evaluated K x) j := rfl

/-- The original marked pointwise injections form the genuine full-enriched cocone. -/
def cocone : Cocone K where
  pt := object K
  ι :=
    { app := injection K
      naturality i j f := by
        apply EnrichedDiagramMap.ext
        funext x
        let ii : (K.obj i).obj x ⟶ colimit (evaluated K x) := colimit.ι (evaluated K x) i
        let ij : (K.obj j).obj x ⟶ colimit (evaluated K x) := colimit.ι (evaluated K x) j
        have h : (K.map f).app x ≫ ij = ii := colimit.w (evaluated K x) f
        exact h.trans (Category.comp_id ii).symm }

end SSet.Marked.EnrichedColimit
