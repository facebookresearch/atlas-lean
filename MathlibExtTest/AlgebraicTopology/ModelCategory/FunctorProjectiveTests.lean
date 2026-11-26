/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective

set_option autoImplicit false
noncomputable section
universe w uJ vJ uC vC

open CategoryTheory HomotopicalAlgebra

namespace MathlibExtTest.FunctorProjective

example {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
    [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [Small.{w} J] [LocallySmall.{w} J] (d : CofibrantGenerationData C κ) :
    ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d

example {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
    [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [Small.{w} J] [LocallySmall.{w} J] (d : CofibrantGenerationData C κ) :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    fibrations (J ⥤ C) = (fibrations C).functorCategory J :=
  FunctorProjective.fibrations_eq d

example {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
    [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [Small.{w} J] [LocallySmall.{w} J] (d : CofibrantGenerationData C κ) (j : J) :
    let _ : CategoryTheory.Limits.HasCoproducts.{w} C := d.I_smallObject.hasCoproducts
    let _ : ∀ i k : J, CategoryTheory.Limits.HasCoproductsOfShape (i ⟶ k) C :=
      fun i k => CategoryTheory.Limits.hasCoproductsOfShape_of_small C (i ⟶ k)
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    (evaluationAdjunctionRight C j).IsQuillenAdjunction :=
  FunctorProjective.evaluation_isQuillenAdjunction d j

-- Callers supply only the actual base generation data at the original cardinal.
-- The provider derives target SOAs, Hom copowers and left acyclicity.
#print axioms FunctorProjective.modelCategory

end MathlibExtTest.FunctorProjective
