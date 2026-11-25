/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyStructure
public import MathlibExt.CategoryTheory.Reedy.FactorizationCorners
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Reedy factorization of simplicial morphisms

A factorization of morphisms of `C` into a `P`-map followed by a `Q`-map, with `P` and `Q`
respecting isomorphisms, gives a factorization of every morphism of simplicial objects into a
Reedy-left map for `P` followed by a Reedy-right map for `Q`: `reedyMapFactorizationData` and its
instance `reedyHasFactorization`. The factorization is the degreewise construction of the generic
Reedy structure, `ReedyStructure.DegreeFactorization.classifiedFactor`, for `SimplexCategoryᵒᵖ`,
whose Reedy classes are `reedyLeft P` and `reedyRight Q` (`reedyLeft_eq_latchingClass`,
`reedyRight_eq_matchingClass`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Factor any simplicial morphism into a Reedy-left map followed by a Reedy-right map. -/
noncomputable def reedyMapFactorizationData
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (P Q : MorphismProperty C)
    [HasPushouts C] [HasPullbacks C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
    [P.HasFactorization Q] [P.RespectsIso] [Q.RespectsIso] :
    (reedyLeft P).MapFactorizationData (reedyRight Q) f :=
  let d := CategoryTheory.ReedyStructure.DegreeFactorization.classifiedFactor reedyStructure f
    (P.factorizationData Q)
  { Z := d.Z
    i := d.i
    p := d.p
    fac := d.fac
    hi := by
      rw [reedyLeft_eq_latchingClass]
      exact d.hi
    hp := by
      rw [reedyRight_eq_matchingClass]
      exact d.hp }

/-- Reedy-left and Reedy-right maps inherit factorizations from the corresponding base-category
morphism properties. -/
noncomputable instance reedyHasFactorization
    (P Q : MorphismProperty C)
    [HasPushouts C] [HasPullbacks C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
    [P.HasFactorization Q] [P.RespectsIso] [Q.RespectsIso] :
    (reedyLeft P).HasFactorization (reedyRight Q) where
  nonempty_mapFactorizationData f := ⟨reedyMapFactorizationData f P Q⟩

end CategoryTheory.SimplicialObject
