/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.RelativeSmallness

/-!# Original families and real common regular-cardinal generation witnesses -/
set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits MorphismProperty Cardinal HomotopicalAlgebra
open CategoryTheory.SmallObject

namespace MathlibExtTest.RelativeCofibrantGeneration

variable {C : Type u} [Category.{v} C] (I J : MorphismProperty C)
  [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : UniformRelativeSourceSmallness.{w} I)
  (hJ : UniformRelativeSourceSmallness.{w} J)

example :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧
      (∀ i : I.toSet, UniformRelativeSourceSmallness.sourceBound hI i < κ) ∧
      (∀ j : J.toSet, UniformRelativeSourceSmallness.sourceBound hJ j < κ) :=
  exists_common_relative_source_bound I J hI hJ

section Eligibility

variable [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
  (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType C)

example :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      I.IsCardinalForSmallObjectArgument κ ∧ J.IsCardinalForSmallObjectArgument κ :=
  exists_common_relative_generation_cardinal I J hI hJ hIteration

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [HasIterationOfShape κ.ord.ToType C]
    (hκ : ∀ i : I.toSet, UniformRelativeSourceSmallness.sourceBound hI i < κ) :
    I.IsCardinalForSmallObjectArgument κ :=
  isCardinalForSmallObjectArgument_of_uniform_bounds I hI κ hκ

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [HasIterationOfShape κ.ord.ToType C]
    (hκ : ∀ i : I.toSet, UniformRelativeSourceSmallness.sourceBound hI i < κ)
    {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => I.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op A)) :=
  (isCardinalForSmallObjectArgument_of_uniform_bounds I hI κ hκ).preservesColimit i hi f c

end Eligibility

section Model

variable [ModelCategory C] [LocallySmall.{w} C] [HasCoproducts.{w} C]
  (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType C)
  (hIrlp : I.rlp = trivialFibrations C) (hJrlp : J.rlp = fibrations C)

example :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      ∃ d : CofibrantGenerationData C κ, d.I = I ∧ d.J = J :=
  exists_cofibrantGenerationData_of_uniform_relative_smallness I J hI hJ hIteration hIrlp hJrlp

example : HasCompatibleCofibrantGeneration.{w} C :=
  hasCompatibleCofibrantGeneration_of_uniform_relative_smallness I J hI hJ hIteration hIrlp hJrlp

example :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      I.IsCardinalForSmallObjectArgument κ ∧ J.IsCardinalForSmallObjectArgument κ ∧
        I.rlp = trivialFibrations C ∧ J.rlp = fibrations C := by
  obtain ⟨κ, hκ, hb, d, hdI, hdJ⟩ :=
    exists_cofibrantGenerationData_of_uniform_relative_smallness I J hI hJ hIteration hIrlp hJrlp
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hb
  exact ⟨κ, hκ, hb, hdI ▸ d.I_smallObject, hdJ ▸ d.J_smallObject, hIrlp, hJrlp⟩

end Model

end MathlibExtTest.RelativeCofibrantGeneration
