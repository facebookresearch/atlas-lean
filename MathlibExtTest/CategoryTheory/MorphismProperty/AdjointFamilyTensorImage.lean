/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamilyTensorImage

/-!
# Public client of tensor transport in a braided category

The property transport uses only the original braiding and its naturality.
The client has no symmetric-category assumption.
-/

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (P : MorphismProperty D) [P.RespectsIso]

example (N : D) {X Y : D} (i : X ⟶ Y) (hi : P (i ▷ N)) : P (N ◁ i) :=
  AdjointFamilyTensorImage.leftTensor_of_right P N i hi
