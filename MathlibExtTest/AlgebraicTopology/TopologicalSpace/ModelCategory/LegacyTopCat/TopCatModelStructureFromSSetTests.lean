/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructureFromSSet

@[expose] public section

/-!
# Conditional TopCat model-structure-from-SSet client

Thin public client for `TopCat.modelCategoryFromSSet` by term application
only. Carries the same three explicit inputs `hHorn`, `hI`, and `hJ`
and invokes the provider directly. Supplies no premise, adds no instance,
and claims no unconditional model structure. The `hI` premise is restricted
to Kan source/target; no arbitrary-map `I.rlp ≤ KanComplex.W` is asserted
because identities on non-Kan objects refute it.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelStructureFromSSetTests

/-- Conditional model-structure-from-SSet client: the three explicit inputs
package the `TopCat` model structure in every universe. -/
noncomputable abbrev modelCategoryFromSSet_client
    (hHorn : TopCat.realizedHornInclusions.{u}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
      {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f)
    (hJ : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    ModelCategory TopCat.{u} :=
  TopCat.modelCategoryFromSSet hHorn hI hJ

section ConcreteUniverses

noncomputable example
    (hHorn : TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{1}} [SSet.KanComplex X]
      [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{1}.rlp f → SSet.KanComplex.W.{1} f)
    (hJ : SSet.modelCategoryQuillen.J.{1}.rlp ⊓ SSet.KanComplex.W.{1} ≤
      SSet.modelCategoryQuillen.I.{1}.rlp) :
    ModelCategory TopCat.{1} :=
  TopCat.modelCategoryFromSSet hHorn hI hJ

noncomputable example
    (hHorn : TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{0}} [SSet.KanComplex X]
      [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{0}.rlp f → SSet.KanComplex.W.{0} f)
    (hJ : SSet.modelCategoryQuillen.J.{0}.rlp ⊓ SSet.KanComplex.W.{0} ≤
      SSet.modelCategoryQuillen.I.{0}.rlp) :
    ModelCategory TopCat.{0} :=
  TopCat.modelCategoryFromSSet hHorn hI hJ

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

#print axioms TopCat.modelCategoryFromSSet
#print axioms modelCategoryFromSSet_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelStructureFromSSetTests
