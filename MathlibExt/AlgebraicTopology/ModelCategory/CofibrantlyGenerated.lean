/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Cofibrant generation data for model categories

The generating families in this file are explicit noncanonical data. They
are packaged at one regular cardinal and are never installed as typeclass
choices.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

/-- Two explicit generating families for a model category at one regular
cardinal. The right-class equalities identify the two model weak
factorization systems; the left-class equalities follow from the existing
model-category WFS API. -/
structure CofibrantGenerationData
    (C : Type u) [Category.{v} C] [ModelCategory C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] where
  I : MorphismProperty C
  J : MorphismProperty C
  I_smallObject : I.IsCardinalForSmallObjectArgument κ
  J_smallObject : J.IsCardinalForSmallObjectArgument κ
  I_rlp : I.rlp = trivialFibrations C
  J_rlp : J.rlp = fibrations C

end HomotopicalAlgebra
