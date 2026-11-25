/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# The cartesian monoidal Kan--Quillen model structure

The selected Kan--Quillen model structure on simplicial sets satisfies the
pushout-product and unit axioms for its existing closed cartesian monoidal
structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

/-- The selected Kan--Quillen model structure is a closed symmetric monoidal
model structure for the cartesian tensor product. -/
noncomputable scoped instance instIsClosedSymmetricMonoidalModelCategory :
    IsClosedSymmetricMonoidalModelCategory SSet.{u} :=
  isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    SSet.{u}
    (by
      intro A B K L i j hi hj
      let _ : Cofibration i := (cofibration_iff i).2 hi
      let _ : Cofibration j := (cofibration_iff j).2 hj
      exact (cofibration_iff _).1
        (SSet.cofibration_pushoutProduct i j))
    (by
      intro A B K L i j hi hj
      have hi' := (mem_trivialCofibrations_iff i).1 hi
      let _ : Cofibration i := hi'.1
      let _ : WeakEquivalence i := hi'.2
      let _ : Cofibration j := (cofibration_iff j).2 hj
      exact SSet.pushoutProduct_mem_trivialCofibrations_of_left i j)
    (by
      intro A B K L i j hi hj
      let _ : Cofibration i := (cofibration_iff i).2 hi
      have hj' := (mem_trivialCofibrations_iff j).1 hj
      let _ : Cofibration j := hj'.1
      let _ : WeakEquivalence j := hj'.2
      exact SSet.pushoutProduct_mem_trivialCofibrations_of_right i j)

end SSet.modelCategoryQuillen
