/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.FunctorOpposite
public import MathlibExt.CategoryTheory.Enriched.StrictComposition

/-!
# Whole composition laws for enriched functors

The strict identity and associativity laws are imported from `StrictComposition`.
The opposite-specific equalities retain the original object functions and all
Hom maps for independent object universes and a braided monoidal enrichment base.
-/

@[expose] public section

noncomputable section
universe w v u₁ u₂ u₃
open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedFunctor

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [EnrichedCategory V A] [EnrichedCategory V B]
    [EnrichedCategory V C]

variable [BraidedCategory V]

/-- Taking opposites keeps the same whole enriched composition in its original order. -/
theorem opposite_comp (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B C) :
    (F.comp V G).opposite = F.opposite.comp V G.opposite := rfl

/-- The opposite of the actual enriched identity is the actual opposite identity. -/
theorem opposite_id : (EnrichedFunctor.id V A).opposite = EnrichedFunctor.id V Aᵒᵖ := rfl

end CategoryTheory.EnrichedFunctor
