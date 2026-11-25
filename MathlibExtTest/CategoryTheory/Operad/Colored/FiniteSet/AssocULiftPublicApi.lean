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

import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.AssocULift

/-!
# Focused O7E assoc-ulift public-contract packet

Pins the stable downstream-facing contract for the
universe-lifted associative operad: it is the canonical lift
of the universe-zero associative operad.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v

-- The lifted assoc operad is the canonical ulift of assoc.
example : SetOperad.assocULift.{v} =
    SetOperad.ulift SetOperad.assoc :=
  rfl
