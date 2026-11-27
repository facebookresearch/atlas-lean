/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductPrimeOneModFour

open MetaMathlibExt

-- The smallest eligible prime already fails one-vanishing.
example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 5)) :=
  not_isMVanishingFamily_sumAddMulProd_one_prime_one_mod_four (by decide) (by decide) (by decide)

-- The theorem also applies to more than one block at a larger eligible prime.
example : ¬ IsMVanishingFamily 3 (sumAddMulProdFamily (1 : ZMod 13)) :=
  not_isMVanishingFamily_sumAddMulProd_one_prime_one_mod_four (by decide) (by decide) (by decide)
