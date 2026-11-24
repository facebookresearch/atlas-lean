/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# comparison arrows with identical inferred endpoints
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC
open CategoryTheory

namespace CategoryTheory

/-- Two arrows with identical original source and target labels. -/
structure ComparisonArrows {C : Type uC} [Category.{vC} C] where
  /-- The original source coefficient object. -/
  source : C
  /-- The original target coefficient object. -/
  target : C
  /-- The first comparison arrow. -/
  left : source ⟶ target
  /-- The second comparison arrow. -/
  right : source ⟶ target

/-- Package the two arrows while retaining the endpoints inferred from their original typed inputs. -/
def comparisonArrowsOfMaps {C : Type uC} [Category.{vC} C]
    {X Y : C} (l r : X ⟶ Y) : ComparisonArrows (C := C) :=
  ⟨X, Y, l, r⟩

end CategoryTheory
