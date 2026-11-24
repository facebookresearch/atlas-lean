/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage

/-!
# Bundled Waldhausen stage consumer tests

Minimal public-API checks for the bundled `Stage` full subcategory:
recovering `IsStage` through the full-subcategory property, full
faithfulness of `forget`, and pointwise evaluation at a concrete `Ar 1`
object with functor identity laws. No low-degree equivalence is claimed.
-/

open CategoryTheory

namespace CategoryTheory
namespace Waldhausen
namespace SConstruction
namespace StageTests

universe v u

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  (n : ℕ)

/-- Recover `IsStage` of the forgotten diagram through the full-subcategory property. -/
example (X : Stage C n) : IsStage n ((forget C n).obj X) :=
  X.property

/-- The forgetful functor is fully faithful. -/
example : (forget C n).FullyFaithful :=
  fullyFaithfulForget C n

/-- Concrete `Ar 1` interval for pointwise evaluation. -/
def testInterval : Ar 1 :=
  interval (0 : Fin 2) 1 (by decide)

/-- Pointwise evaluation lands in `C`. -/
example (X : Stage C 1) : C :=
  (eval C 1 testInterval).obj X

/-- Pointwise evaluation preserves identity via public functor laws. -/
example (X : Stage C 1) :
    (eval C 1 testInterval).map (𝟙 X) = 𝟙 ((eval C 1 testInterval).obj X) :=
  (eval C 1 testInterval).map_id X

end StageTests
end SConstruction
end Waldhausen
end CategoryTheory
