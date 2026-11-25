/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ScalarTensor

/-! # The scalar tensor bifunctor on enriched diagrams -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Scalar tensoring retains all scalar and diagram maps. -/
def tensorBifunctor : V ⥤ EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A where
  obj M := EnrichedFunctorCat.tensorLeft M
  map h :=
    { app F := scalarTensorMap h F
      naturality _ _ j := scalarTensorMap_diagram_naturality h j }
  map_id M := by
    apply NatTrans.ext
    funext F
    exact scalarTensorMap_id M F
  map_comp h k := by
    apply NatTrans.ext
    funext F
    exact scalarTensorMap_comp h k F

end CategoryTheory.EnrichedFunctorCat
