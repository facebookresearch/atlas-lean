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

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import MathlibExt.Algebra.Category.FGProjectiveCat.Inclusion
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberExactFunctor
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategoryZero

/-!
# Consumer checks for `cofiberSequenceFunctor`

Focused public-API checks for `cofiberSequenceFunctor` along the genuinely
non-identity exact inclusion `FGProjectiveCat.inclusion ℚ`: downstream
zero-object inference, and both transported legs — the underlying `0 → 1`
map is the image of the source leg and the underlying `1 → 2` map is the
image of the second/quotient leg. Uses the lift as a black box; no
unfolding, no identity case, no Cartan/G-theory comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberExactFunctorTests

local instance : WaldhausenCategoryWithoutGluing (FGProjectiveCat ℚ) :=
  ExactCategory.waldhausenCategory _

local instance : WaldhausenCategoryWithoutGluing (FGModuleCat ℚ) :=
  ExactCategory.waldhausenCategory _

-- Downstream zero-object instance; fails if the `ContainsZero` transfer is missing.
example : Limits.HasZeroObject (CofiberSequenceCategory (FGProjectiveCat ℚ)) :=
  inferInstance

-- Underlying `0 → 1` map is the image of the source leg.
example (S : CofiberSequenceCategory (FGProjectiveCat ℚ)) :
    (((CofiberSequenceCategory.forget (FGModuleCat ℚ)).obj
      ((cofiberSequenceFunctor (FGProjectiveCat.inclusion ℚ)).obj S)).map' 0 1) =
    ((FGProjectiveCat.inclusion ℚ).map
      (((CofiberSequenceCategory.forget (FGProjectiveCat ℚ)).obj S).map' 0 1)) :=
  rfl

-- Underlying `1 → 2` map is the image of the second/quotient leg.
example (S : CofiberSequenceCategory (FGProjectiveCat ℚ)) :
    (((CofiberSequenceCategory.forget (FGModuleCat ℚ)).obj
      ((cofiberSequenceFunctor (FGProjectiveCat.inclusion ℚ)).obj S)).map' 1 2) =
    ((FGProjectiveCat.inclusion ℚ).map
      (((CofiberSequenceCategory.forget (FGProjectiveCat ℚ)).obj S).map' 1 2)) :=
  rfl

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberExactFunctorTests
