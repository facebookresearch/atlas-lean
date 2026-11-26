/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated

/-!
# Selected functorial factorizations from cofibrant generation data

The two records use the specified generating families, cardinal, and ordinal bottom.
`FunctorialFactorizationData.ofLE` changes only the membership proofs: the middle functor and
both natural transformations are definitionally those of `SmallObject.functorialFactorizationData`.
Neither record is obtained by choosing a witness of `HasFunctorialFactorization`.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The actual I-factorization at the supplied cardinal, with only membership transported. -/
noncomputable def cofibrantFactorizationData (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact (SmallObject.functorialFactorizationData d.I κ).ofLE
    (by rw [d.I_rlp, trivialFibrations_llp]) d.I_rlp.le

/-- The actual J-factorization at the same supplied cardinal, without choosing new maps. -/
noncomputable def fibrantFactorizationData (d : CofibrantGenerationData C κ) :
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  letI : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
  exact (SmallObject.functorialFactorizationData d.J κ).ofLE
    (by rw [d.J_rlp, fibrations_llp]) d.J_rlp.le

end HomotopicalAlgebra.CofibrantGenerationData
