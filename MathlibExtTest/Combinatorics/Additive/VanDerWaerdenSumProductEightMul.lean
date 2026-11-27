/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductEightMul

open MetaMathlibExt

-- Both parameters are at their smallest allowed values.
example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 16)) :=
  not_isMVanishingFamily_sumAddMulProd_one_eight_mul (u := 2) (by decide) (by decide)

-- The result also applies at a larger modulus and block count.
example : ¬ IsMVanishingFamily 3 (sumAddMulProdFamily (1 : ZMod 24)) :=
  not_isMVanishingFamily_sumAddMulProd_one_eight_mul (u := 3) (by decide) (by decide)
