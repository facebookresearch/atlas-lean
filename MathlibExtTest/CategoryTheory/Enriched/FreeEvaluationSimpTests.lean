/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

set_option autoImplicit false
noncomputable section
universe uV vV uA
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (a b c : A) (X : V) :
    MonoidalClosed.uncurry
      ((EnrichedFunctorCat.Free.object a X).toEnrichedFunctor.map b c) =
        EnrichedFunctorCat.Free.action a X b c := by simp
