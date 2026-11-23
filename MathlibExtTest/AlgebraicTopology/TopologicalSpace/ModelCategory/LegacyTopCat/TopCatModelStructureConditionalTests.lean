/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructureConditional

@[expose] public section

/-!
# Conditional TopCat model-structure client

Thin public client for `TopCat.modelCategoryConditional` by term application
only. Carries the same explicit compatibility equalities `hFib` and `hCof`
and invokes the provider directly. Supplies no premise, manufactures neither
equality, adds no instance, and claims no unconditional model structure.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelStructureConditionalTests

/-- Conditional model-structure client: the two explicit compatibility
equalities package the `TopCat` model structure in every universe. -/
noncomputable abbrev modelCategoryConditional_client
    (hFib : (TopCat.realizedHornInclusions.rlp ⊓ TopCat.weakHomotopyEquivalences :
      MorphismProperty TopCat.{u}) = TopCat.realizedBoundaryInclusions.rlp)
    (hCof : (TopCat.realizedBoundaryInclusions.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences : MorphismProperty TopCat.{u}) =
      TopCat.realizedHornInclusions.rlp.llp) :
    ModelCategory TopCat.{u} :=
  TopCat.modelCategoryConditional hFib hCof

section ConcreteUniverses

noncomputable example
    (hFib : (TopCat.realizedHornInclusions.rlp ⊓
      TopCat.weakHomotopyEquivalences : MorphismProperty TopCat.{1}) =
        TopCat.realizedBoundaryInclusions.rlp)
    (hCof : (TopCat.realizedBoundaryInclusions.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences : MorphismProperty TopCat.{1}) =
        TopCat.realizedHornInclusions.rlp.llp) :
    ModelCategory TopCat.{1} :=
  TopCat.modelCategoryConditional hFib hCof

noncomputable example
    (hFib : (TopCat.realizedHornInclusions.rlp ⊓
      TopCat.weakHomotopyEquivalences : MorphismProperty TopCat.{0}) =
        TopCat.realizedBoundaryInclusions.rlp)
    (hCof : (TopCat.realizedBoundaryInclusions.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences : MorphismProperty TopCat.{0}) =
        TopCat.realizedHornInclusions.rlp.llp) :
    ModelCategory TopCat.{0} :=
  TopCat.modelCategoryConditional hFib hCof

end ConcreteUniverses

section NoInstance

example : True := by
  fail_if_success
    let _ : ModelCategory TopCat.{u} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{1} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{0} := inferInstance
  trivial

end NoInstance

#print axioms TopCat.modelCategoryConditional
#print axioms modelCategoryConditional_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelStructureConditionalTests
