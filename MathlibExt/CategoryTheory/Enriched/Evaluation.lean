/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FunctorCategory

/-!
# Evaluation of genuine enriched functors

Evaluation keeps the actual object and ordinary component of each genuine
unit-graded transformation. The source requires only its original enrichment.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uA uV vV

open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Evaluation on the genuine enriched-functor category uses the original components. -/
def evaluation (a : A) : EnrichedFunctorCat V A ⥤ V where
  obj F := F.toEnrichedFunctor.obj a
  map f := component f a
  map_id F := component_id F a
  map_comp f g := component_comp f g a

/-- Evaluation retains the original enriched object. -/
@[simp]
theorem evaluation_obj (a : A) (F : EnrichedFunctorCat V A) :
    (evaluation a).obj F = F.toEnrichedFunctor.obj a := rfl

/-- Evaluation retains the actual component of a genuine transformation. -/
@[simp]
theorem evaluation_map (a : A) {F G : EnrichedFunctorCat V A} (f : F ⟶ G) :
    (evaluation a).map f = component f a := rfl

end CategoryTheory.EnrichedFunctorCat
