/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverHomologyOne
public import Mathlib.CategoryTheory.SingleObj

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

/-- The public client retains an arbitrary Kan source and its original vertex. -/
example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    IsZero ((SSet.KanComplex.nativeCover X x).homology
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 1) :=
  SSet.KanComplex.nativeCoverHomologyOne_isZero X x

/-- The original one-object nerve cover is included for an arbitrary group in
the same universe, with no commutativity or H-space assumption. -/
example (G : Type u) [Group G] :
    IsZero ((SSet.KanComplex.nativeCover
      (CategoryTheory.nerve (SingleObj G))
      (ComposableArrows.mk₀ (SingleObj.star G))).homology
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 1) := by
  let _ : SSet.KanComplex (CategoryTheory.nerve (SingleObj G)) :=
    SSet.kanComplex_nerve_of_groupoid (SingleObj G)
  exact SSet.KanComplex.nativeCoverHomologyOne_isZero _ _

end
