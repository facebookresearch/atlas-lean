/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.Basic

/-!
# Homotopy function complexes

This file gives the conventional two-object name for the chosen derived
mapping object `sHom (Q X) (R Y)`.  It is a transparent facade for the fixed
functorial-replacement presentation, not a canonical equality class or a
strict mapping object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- The chosen homotopy function complex `sHom (Q X) (R Y)`. -/
noncomputable abbrev homotopyFunctionComplex (X Y : C) : SSet.{v} :=
  ((derivedMappingObject (C := C)).obj (.op X)).obj Y

end HomotopicalAlgebra
