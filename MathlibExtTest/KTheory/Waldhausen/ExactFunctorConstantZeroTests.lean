/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Core-only clients for exact constant zero functors

The original constant functor retains independent source and target
object and morphism universes. The target is its actual selected zero,
and all original objects and maps have their literal constant readouts.
No realization or first-quotient module is imported.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uC vC uD vD

namespace MathlibExtTest.KTheory.Waldhausen.ExactFunctorConstantZeroTests

variable (C : Type uC) [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable (D : Type uD) [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]

/-- The actual constant-zero functor is exact with all four independent universe roles. -/
theorem originalConstantZeroExact : ((Functor.const C).obj (0 : D)).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.constantZero C D

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] in
/-- Every complete original source object maps to the actual chosen target zero. -/
theorem originalConstantObject (X : C) :
    ((Functor.const C).obj (0 : D)).obj X = (0 : D) := rfl

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] in
/-- Every complete original source morphism maps to the actual target zero identity. -/
theorem originalConstantMap {X Y : C} (f : X ⟶ Y) :
    ((Functor.const C).obj (0 : D)).map f = 𝟙 (0 : D) := rfl

end MathlibExtTest.KTheory.Waldhausen.ExactFunctorConstantZeroTests

end
