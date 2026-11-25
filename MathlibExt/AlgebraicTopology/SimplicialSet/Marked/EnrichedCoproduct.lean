/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimits
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Actual marked enriched coproducts and their full injection calculus

The object is the original marked pointwise coproduct. Its genuine
injections, descent and whole-Hom extensionality come from the proved
full enriched colimit, with no model-category or coend outcome assumed.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace SSet.Marked.EnrichedCoproduct

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C] {I : Type u}
    (E : I → EnrichedDiagram C)

local instance evaluatedHasColimit (x : C) : HasColimit (EnrichedColimit.evaluated (Discrete.functor E) x) :=
  inferInstance

/-- The actual whole marked coproduct diagram uses its original pointwise marked colimits. -/
def object : EnrichedDiagram C := EnrichedColimit.object (Discrete.functor E)

/-- The original marked summand injection is the whole enriched colimit injection. -/
def ι (i : I) : E i ⟶ object E := EnrichedColimit.injection (Discrete.functor E) (Discrete.mk i)

/-- A family of entire enriched maps is its actual discrete enriched cocone. -/
def cocone {X : EnrichedDiagram C} (f : ∀ i : I, E i ⟶ X) : Cocone (Discrete.functor E) where
  pt := X
  ι := Discrete.natTrans (fun i => f i.as)

/-- The original coproduct descends every whole marked family of summand maps. -/
def desc {X : EnrichedDiagram C} (f : ∀ i : I, E i ⟶ X) : object E ⟶ X :=
  EnrichedColimit.desc (Discrete.functor E) (cocone E f)

/-- Each entire original summand injection factors through the same full enriched descent. -/
theorem ι_desc {X : EnrichedDiagram C} (f : ∀ i : I, E i ⟶ X) (i : I) :
    ι E i ≫ desc E f = f i :=
  EnrichedColimit.injection_desc (Discrete.functor E) (cocone E f) (Discrete.mk i)

/-- The original marked summand injections detect equality of whole enriched maps. -/
theorem hom_ext {X : EnrichedDiagram C} {f g : object E ⟶ X}
    (h : ∀ i : I, ι E i ≫ f = ι E i ≫ g) : f = g :=
  (EnrichedColimit.isColimit (Discrete.functor E)).hom_ext (fun i => h i.as)

end SSet.Marked.EnrichedCoproduct
