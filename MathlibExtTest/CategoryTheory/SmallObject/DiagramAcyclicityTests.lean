/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.DiagramAcyclicity

set_option autoImplicit false
noncomputable section

universe w uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace DiagramAcyclicityTests

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]
  (P Q : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [Small.{w} J] [LocallySmall.{w} J]
  (hP : P.IsCardinalForSmallObjectArgument κ) (hPQ : P ≤ Q)
  [Q.IsStableUnderRetracts] [Q.IsStableUnderCoproducts.{w}]
  [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]

-- Only the actual base cardinal and closed base property are provided.
-- No target model, target SOA, or desired evaluated membership is a premise.
example (k : J) {X Y : J ⥤ C} (f : X ⟶ Y)
    (hf : (MorphismProperty.adjointFamilyGenerators
      (fun j : J => evaluationLeftAdjoint C j) P).rlp.llp f) :
    Q (f.app k) :=
  (MorphismProperty.freeDiagrams_leftClass_evaluation_le P Q κ hP hPQ k) f hf

example (W : MorphismProperty C) (hQW : Q ≤ W) {X Y : J ⥤ C} (f : X ⟶ Y)
    (hf : (MorphismProperty.adjointFamilyGenerators
      (fun j : J => evaluationLeftAdjoint C j) P).rlp.llp f) :
    ∀ k : J, W (f.app k) :=
  (MorphismProperty.freeDiagrams_leftClass_le_functorCategory P Q W κ hP hPQ hQW) f hf

#check @MorphismProperty.freeDiagrams_leftClass_evaluation_le
#check @MorphismProperty.freeDiagrams_leftClass_le_functorCategory
#print axioms MorphismProperty.freeDiagrams_leftClass_evaluation_le
#print axioms MorphismProperty.freeDiagrams_leftClass_le_functorCategory

end DiagramAcyclicityTests
