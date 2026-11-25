/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.CombinatorialTests

section FixedSourceRank

variable {M : Type u} [Category.{v} M]
variable (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable M κLP]
variable (I J : MorphismProperty M) [I.HasSmallObjectArgument.{w}]
  [J.HasSmallObjectArgument.{w}] (fixed : Type w)

/-- A bare category and the original source families retain the fixed bound and all sources;
no model category or functor category is supplied. -/
theorem fixedBoundAndOriginalSources :
    ∃ (ρ : Cardinal.{w}) (_ : Fact ρ.IsRegular) (_ : OrderBot ρ.ord.ToType),
      κLP < ρ ∧ HasCardinalLT fixed ρ ∧ IsCardinalLocallyPresentable M ρ ∧
      (∀ i : I.toSet, IsCardinalPresentable i.1.left ρ) ∧
      (∀ j : J.toSet, IsCardinalPresentable j.1.left ρ) ∧
      I.IsCardinalForSmallObjectArgument ρ ∧ J.IsCardinalForSmallObjectArgument ρ :=
  exists_common_generation_cardinal_from_sources κLP I J fixed

end FixedSourceRank

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
variable [OrderBot κ.ord.ToType]

section ExplicitPacket

variable (hC : IsCardinalLocallyPresentable C κ)
variable (G : CofibrantGenerationData C κ)

example : IsCombinatorialModelCategory.{w} C where
  exists_cardinal := ⟨κ, inferInstance, inferInstance, hC, ⟨G⟩⟩

end ExplicitPacket

section ConventionalConstructor

variable [IsLocallyPresentable.{w} C]
variable (I J : MorphismProperty C)
variable [I.HasSmallObjectArgument.{w}]
variable [J.HasSmallObjectArgument.{w}]

example (hI : I.rlp = trivialFibrations C)
    (hJ : J.rlp = fibrations C) :
    IsCombinatorialModelCategory.{w} C :=
  isCombinatorialModelCategory_of_generators I J hI hJ

end ConventionalConstructor

section ExistentialBoundary

variable [IsCombinatorialModelCategory.{w} C]

example :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular)
      (_ : OrderBot κ.ord.ToType),
      IsCardinalLocallyPresentable C κ ∧
        Nonempty (CofibrantGenerationData C κ) :=
  IsCombinatorialModelCategory.exists_cardinal

example (_I : MorphismProperty C) : True := by
  fail_if_success
    have _ : _I.HasSmallObjectArgument.{w} := inferInstance
  fail_if_success
    have _ : IsLocallyPresentable.{w} C := inferInstance
  fail_if_success
    have _ : IsCardinalLocallyPresentable C κ := inferInstance
  trivial

end ExistentialBoundary

section SSet

open scoped SSet.modelCategoryQuillen

attribute [local instance]
  Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

example : Nonempty
    (CofibrantGenerationData SSet.{u} Cardinal.aleph0.{u}) := by
  let G : CofibrantGenerationData SSet.{u} Cardinal.aleph0.{u} :=
    { I := SSet.modelCategoryQuillen.I
      J := SSet.modelCategoryQuillen.J
      I_smallObject := inferInstance
      J_smallObject := inferInstance
      I_rlp := by
        rw [← cofibrations_rlp,
          SSet.modelCategoryQuillen.cofibrations_eq,
          ← SSet.modelCategoryQuillen.llp_rlp_I, rlp_llp_rlp]
      J_rlp := SSet.modelCategoryQuillen.fibrations_eq.symm }
  exact ⟨G⟩

example : IsCombinatorialModelCategory.{0} SSet.{0} := by
  let G : CofibrantGenerationData SSet.{0} Cardinal.aleph0.{0} :=
    { I := SSet.modelCategoryQuillen.I
      J := SSet.modelCategoryQuillen.J
      I_smallObject := inferInstance
      J_smallObject := inferInstance
      I_rlp := by
        rw [← cofibrations_rlp,
          SSet.modelCategoryQuillen.cofibrations_eq,
          ← SSet.modelCategoryQuillen.llp_rlp_I, rlp_llp_rlp]
      J_rlp := SSet.modelCategoryQuillen.fibrations_eq.symm }
  exact
    { exists_cardinal :=
        ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance, ⟨G⟩⟩ }

end SSet

section UniverseClients

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [IsCombinatorialModelCategory.{1} C₁]
variable {C₀ : Type} [Category C₀] [ModelCategory C₀]
variable [IsCombinatorialModelCategory.{0} C₀]

example : Prop := IsCombinatorialModelCategory.{1} C₁
example : Prop := IsCombinatorialModelCategory.{0} C₀

end UniverseClients

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.commonGenerationCardinal
  trivial

end HomotopicalAlgebra.CombinatorialTests

#check HomotopicalAlgebra.IsCombinatorialModelCategory
#check HomotopicalAlgebra.isCombinatorialModelCategory_of_generators
#print axioms HomotopicalAlgebra.IsCombinatorialModelCategory
#print axioms HomotopicalAlgebra.isCombinatorialModelCategory_of_generators
