/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Dependent map congruence for enriched functors

Equality of genuine enriched functors transports the entire Hom-object map,
including its dependent target objects. Source and target are plain enriched
categories with independent universes.
-/

@[expose] public section

set_option autoImplicit false

universe uV vV uC uD

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} {D : Type uD}
  [EnrichedCategory V C] [EnrichedCategory V D]

/-- Equal enriched functors have heterogeneously equal full Hom-object maps. -/
theorem map_heq_of_eq (F G : EnrichedFunctor V C D) (h : F = G) (a b : C) :
    F.map a b ≍ G.map a b := by
  cases h
  rfl

end CategoryTheory.EnrichedFunctor
