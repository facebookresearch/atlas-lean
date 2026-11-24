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

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import MathlibExt.CategoryTheory.ExactCategory.Split

/-!
# Exact monoidal categories

For a braided monoidal additive category equipped with an exact structure, the tensor
product is biexact when tensoring on the left preserves admissible exact sequences (hence
on the right by braiding). Mathlib encodes additive categories as `Preadditive` with
`HasZeroObject` and `HasBinaryBiproducts`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe v u

namespace CategoryTheory.ExactCategory

/-- The tensor product is exact in each variable; for a braided additive category left
    exactness implies right exactness. -/
class IsTensorBiexact (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] : Prop where
  /-- Tensoring on the left preserves exactness -/
  map_tensorLeft (W : C) {S : ShortComplex C} :
    IsAdmissibleExact S → IsAdmissibleExact (S.map (tensorLeft W))

/-- The split exact structure is tensor-biexact since `tensorLeft` is additive.
This is a `theorem`, not a global instance, mirroring `splitExactCategory`. -/
theorem splitIsTensorBiexact
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] :
    @IsTensorBiexact C _ _ _ _ (splitExactCategory (C := C)) _ _ _ :=
  letI : ExactCategory C := splitExactCategory (C := C)
  { map_tensorLeft := fun W S hS =>
      isSplitAdmissibleExact_map (F := tensorLeft W) S hS }

end CategoryTheory.ExactCategory
