/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramComponentIso

/-!
# Actual evaluated colimits determine whole enriched colimits

The existing pointwise construction gives the native comparison to an
original full enriched cocone. When its actual evaluated cocones are
colimits, the component comparisons are their genuine colimit
isomorphisms. The proved whole component-inverse calculus then makes
the original cocone a full enriched colimit, retaining all injections
and all original Hom naturality.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Actual marked colimit universal properties at every original source object give the whole enriched
  colimit of that same original cocone. -/
def enrichedIsColimitOfEvaluation {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] {K : J ⥤ EnrichedDiagram C} (q : Cocone K)
    (h : ∀ x : C, IsColimit ((enrichedDiagramEvaluation C x).mapCocone q)) : IsColimit q := by
  let _ (x : C) : HasColimit (EnrichedColimit.evaluated K x) :=
    ⟨⟨(enrichedDiagramEvaluation C x).mapCocone q, h x⟩⟩
  let d := EnrichedColimit.desc K q
  let _ : ∀ x : C, IsIso (d.app x) := fun x => by
    let e := (colimit.isColimit (EnrichedColimit.evaluated K x)).coconePointUniqueUpToIso (h x)
    change IsIso e.hom
    infer_instance
  let e : EnrichedColimit.object K ≅ q.pt := enrichedDiagramAsIsoOfComponents d
  exact IsColimit.ofIsoColimit (EnrichedColimit.isColimit K)
    (Cocone.ext e (fun j => EnrichedColimit.injection_desc K q j))

end SSet.Marked
