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

public import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.ULift
public import MathlibExt.CategoryTheory.Operad.FiniteSet.Assoc

/-!
# Universe-polymorphic associative operad

This module retains the definitionally transparent universe-zero associative operad and exposes
its canonical lift to any operation universe through the general one-color and colored-operad
lifting machinery.
-/

@[expose] public section

namespace CategoryTheory.Operad.SetOperad

universe v

/-- The associative operad lifted canonically into operation universe `v`. -/
noncomputable abbrev assocULift : SetOperad.{v} :=
  SetOperad.ulift SetOperad.assoc

end CategoryTheory.Operad.SetOperad
