/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Coefficient evaluation of the global injective right classes

The original Hom-indexed free maps lie in the objectwise coefficient left
class. Native whole-square lifting transposition at each original index and
the coefficient WFS give the right-class bounds and their weak consequence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe w uK vK uM vM

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

section FreeImages

variable {K : Type uK} [Category.{vK} K] {M : Type uM} [Category.{vM} M]
  [∀ a b : K, HasCoproductsOfShape (a ⟶ b) M]

private theorem evaluationFreeMap_mem_functorCategory (P : MorphismProperty M)
    [∀ a b : K, P.IsStableUnderCoproductsOfShape (a ⟶ b)]
    {A B : M} (i : A ⟶ B) (hi : P i) (k : K) :
    P.functorCategory K ((evaluationLeftAdjoint M k).map i) := by
  intro t
  have hMap : ((evaluationLeftAdjoint M k).map i).app t =
      Limits.Sigma.map (fun _ : k ⟶ t => i) := by
    apply Limits.Sigma.hom_ext
    intro h
    simp [evaluationLeftAdjoint]
  rw [hMap]
  exact P.colimMap
    (X := Discrete.functor (fun _ : k ⟶ t => A))
    (Y := Discrete.functor (fun _ : k ⟶ t => B))
    (Discrete.natTrans (fun _ => i)) (fun _ => hi)

end FreeImages

namespace HomotopicalAlgebra

variable (K : Type uK) [Category.{vK} K] [LocallySmall.{w} K]
  (M : Type uM) [Category.{vM} M] [ModelCategory M] [HasCoproducts.{w} M]

/-- Both global injective right classes give the actual coefficient right
classes at every original evaluation, without an injective diagram model. -/
theorem injectiveDiagram_rightClasses_le_pointwise :
    (((trivialCofibrations M).functorCategory K).rlp ≤
      (fibrations M).functorCategory K) ∧
    (((cofibrations M).functorCategory K).rlp ≤
      (trivialFibrations M).functorCategory K) := by
  let _ : ∀ a b : K, HasCoproductsOfShape (a ⟶ b) M :=
    fun a b => hasCoproductsOfShape_of_small M (a ⟶ b)
  constructor
  · intro X Y f hf k
    rw [← trivialCofibrations_rlp M]
    intro A B i hi
    exact ((evaluationAdjunctionRight M k).hasLiftingProperty_iff i f).mp
      (hf ((evaluationLeftAdjoint M k).map i)
        (evaluationFreeMap_mem_functorCategory (trivialCofibrations M) i hi k))
  · intro X Y f hf k
    rw [← cofibrations_rlp M]
    intro A B i hi
    exact ((evaluationAdjunctionRight M k).hasLiftingProperty_iff i f).mp
      (hf ((evaluationLeftAdjoint M k).map i)
        (evaluationFreeMap_mem_functorCategory (cofibrations M) i hi k))

/-- The global right orthogonal of the objectwise coefficient cofibrations
consists of original objectwise coefficient weak equivalences. -/
theorem injectiveDiagram_cofibrations_rlp_le_weak :
    ((cofibrations M).functorCategory K).rlp ≤
      (weakEquivalences M).functorCategory K := by
  intro X Y f hf k
  exact ((injectiveDiagram_rightClasses_le_pointwise K M).2 f hf k).2

end HomotopicalAlgebra
