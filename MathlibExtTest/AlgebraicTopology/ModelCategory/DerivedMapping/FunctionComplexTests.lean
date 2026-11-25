/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.FunctionComplex

/-! Tests for the generic homotopy-function-complex facade. -/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.DerivedMapping

section IndependentUniverses

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

#check @HomotopicalAlgebra.homotopyFunctionComplex.{v, u}

example (X Y : C) : SSet.{v} :=
  HomotopicalAlgebra.homotopyFunctionComplex X Y

example (X Y : C) :
    HomotopicalAlgebra.homotopyFunctionComplex X Y =
      ((derivedMappingObject (C := C)).obj (.op X)).obj Y :=
  rfl

example {X X' : C} (f : X ⟶ X') (Y : C) :
    HomotopicalAlgebra.homotopyFunctionComplex X' Y ⟶
      HomotopicalAlgebra.homotopyFunctionComplex X Y :=
  derivedMappingPrecomp (C := C) f Y

example (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    HomotopicalAlgebra.homotopyFunctionComplex X Y ⟶
      HomotopicalAlgebra.homotopyFunctionComplex X Y' :=
  derivedMappingPostcomp (C := C) X g

#check @derivedMappingPrecomp_id
#check @derivedMappingPrecomp_comp
#check @derivedMappingPostcomp_id
#check @derivedMappingPostcomp_comp
#check @derivedMappingPrecomp_postcomp

example (X Y : C) : SSet.{v} :=
  SimplicialCategory.sHom X Y

end IndependentUniverses

section LargeObjectsSmallHoms

variable {C : Type 1} [Category.{0} C] [ModelCategory C]
  [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

example (X Y : C) : SSet.{0} :=
  HomotopicalAlgebra.homotopyFunctionComplex X Y

end LargeObjectsSmallHoms

section UniverseZero

variable {C : Type 0} [Category.{0} C] [ModelCategory C]
  [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

#check @HomotopicalAlgebra.homotopyFunctionComplex.{0, 0}

example (X Y : C) : SSet.{0} :=
  HomotopicalAlgebra.homotopyFunctionComplex X Y

end UniverseZero

section Nonclaims

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.derivedMappingSpace

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyFunctionComplexPrecomp

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyFunctionComplexPostcomp

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyFunctionComplex_eq_sHom

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyFunctionComplexComparison

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyFunctionComplexTensor

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyFunctionComplexCotensor

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.mappingSpectrum

end Nonclaims

#print axioms HomotopicalAlgebra.homotopyFunctionComplex

end MathlibExtTest.AlgebraicTopology.ModelCategory.DerivedMapping
