/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFactorization.ChoiceComparison

/-!
# Tests of the explicit historical and generic Reedy choices
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SimplicialObject

open ReedyR4DegreeStagePreflight (DegreeLT PartialFactorization)

universe v u

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable {X Y : SimplicialObject C} (f : X ⟶ Y) (P Q : MorphismProperty C)
variable [P.HasFactorization Q] [P.RespectsIso] [Q.RespectsIso]

local notation "Historical" => ReedyR4OneDegreeFunctorPreflight.reedyMapFactorizationData
local notation "Generic" => CategoryTheory.ReedyStructure.DegreeFactorization.classifiedFactor

example (n : ℕ) : PartialFactorization f n :=
  ReedyR4OneDegreeFunctorPreflight.stages f P Q n

example : SmallCategory (DegreeLT 0) := inferInstance

example : (Historical f P Q).Z = ReedyR4OneDegreeFunctorPreflight.globalMiddle f P Q := rfl
example : (Historical f P Q).i = ReedyR4OneDegreeFunctorPreflight.globalI f P Q := rfl
example : (Historical f P Q).p = ReedyR4OneDegreeFunctorPreflight.globalP f P Q := rfl
example : (Historical f P Q).i ≫ (Historical f P Q).p = f := (Historical f P Q).fac
example : reedyLeft P (Historical f P Q).i := (Historical f P Q).hi
example : reedyRight Q (Historical f P Q).p := (Historical f P Q).hp

example : (reedyMapFactorizationData f P Q).Z =
    (Generic reedyStructure f (P.factorizationData Q)).Z := rfl

example : (reedyMapFactorizationData f P Q).i =
    (Generic reedyStructure f (P.factorizationData Q)).i := rfl

example : (reedyMapFactorizationData f P Q).p =
    (Generic reedyStructure f (P.factorizationData Q)).p := rfl

example : (reedyLeft P).HasFactorization (reedyRight Q) := inferInstance

example {a b : ℕ} (g : op ⦋a⦌ ⟶ op ⦋b⦌) :
    ReedyR4OneDegreeFunctorPreflight.canonicalSimplexFactor g =
      SimplexCategory.reedyStructure.mapFactorizationData g.unop :=
  ReedyR4OneDegreeFunctorPreflight.canonicalSimplexFactor_eq_native g

end CategoryTheory.SimplicialObject
