/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping

/-!
# Raw local tests on simplicial presheaves

These definitions use the actual fixed-universe mapping end and the original
injective model. They do not require a resolution of the localizing family or
a localized model. The derived comparison theorems are in `LocalTests`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory HomotopicalAlgebra

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i}

/-- The original raw local test is defined at every original target. -/
def isRawLocal (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) : Prop :=
  ∀ j, SSet.realizationWeakEquivalences (innerHomPre (S j).hom Z)

/-- Original local-fibrant objects use the actual injective model and raw tests. -/
def isOriginalLocalFibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) : Prop := IsFibrant Z ∧ isRawLocal S Z

/-- Every original arrow is tested by the raw end into every actual local-fibrant object. -/
def originalLocalEquivalences (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  fun _ _ f => ∀ Z, isOriginalLocalFibrant S Z →
    SSet.realizationWeakEquivalences (innerHomPre f Z)

end SimplicialPresheaf.InjectiveKan
