/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageAdditive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Subtraction under the actual ind-sheaf proper direct image

The additivity theorem implies preservation of subtraction of morphisms.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2/3.2/3.3;
Kashiwara--Schapira, Ind-sheaves.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageAdditive

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open WantedExt.AlgebraicGeometry.IndSheafSourceRequests

example (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    (A B : IndSheaf k X) (a b : A ⟶ B) :
    (indProperImage k f P D).map (a - b) =
      (indProperImage k f P D).map a - (indProperImage k f P D).map b := by
  have := actual_ind_proper_image_additive k X Y f P D
  exact (indProperImage k f P D).map_sub

end MathlibExtTest.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageAdditive
