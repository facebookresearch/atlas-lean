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

public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import MathlibExt.CategoryTheory.ExactCategory.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# Monoidal structure on `FGProjectiveCat`

For a commutative ring `R`, `FGProjectiveCat R` is an additive symmetric monoidal category,
inheriting the symmetric monoidal structure from `ModuleCat R`. Via
`ObjectProperty.IsMonoidal` this yields `MonoidalCategory`, `BraidedCategory`,
`SymmetricCategory`, `MonoidalPreadditive`, and `MonoidalLinear R`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- `isFGProjective` is monoidal: `R` is finite projective and tensor products preserve the
property, so `FGProjectiveCat R` inherits `MonoidalPreadditive` and symmetric monoidal
structure. -/
instance isFGProjective_isMonoidal :
    (isFGProjective R).IsMonoidal where
  prop_unit := by
    constructor
    · exact Module.Finite.self R
    · infer_instance
  prop_tensor X Y hX hY := by
    have : Module.Finite R X := hX.1
    have : Module.Finite R Y := hY.1
    have : Module.Projective R X := hX.2
    have : Module.Projective R Y := hY.2
    constructor
    · exact Module.Finite.tensorProduct R X Y
    · exact Module.Projective.tensorProduct

/-- The split exact structure on `FGProjectiveCat` is tensor-biexact. -/
instance : CategoryTheory.ExactCategory.IsTensorBiexact (FGProjectiveCat.{u} R) :=
  CategoryTheory.ExactCategory.splitIsTensorBiexact (FGProjectiveCat.{u} R)

end ModuleCat
