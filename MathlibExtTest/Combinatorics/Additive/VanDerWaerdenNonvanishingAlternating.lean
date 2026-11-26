/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenNonvanishingAlternating

open MetaMathlibExt

-- The obstruction already prevents one vanishing block modulo five.
example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (2 : ZMod 5)) :=
  not_isMVanishingFamily_sumAddMulProd_of_ne (by decide) 2
    (by decide) (by decide) (by decide) (by decide)

-- The coefficient need not be a unit: two is a zero divisor modulo eight.
example : ¬ IsMVanishingFamily 3 (sumAddMulProdFamily (2 : ZMod 8)) :=
  not_isMVanishingFamily_sumAddMulProd_of_ne (by decide) 2
    (by decide) (by decide) (by decide) (by decide)
