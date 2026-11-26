/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductNine

open MetaMathlibExt

-- Both parameters are at their smallest allowed values.
example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 9)) :=
  not_isMVanishingFamily_sumAddMulProd_one_nine_mul (u := 1) (by decide) (by decide)

-- The result also applies at a larger modulus and block count.
example : ¬ IsMVanishingFamily 3 (sumAddMulProdFamily (1 : ZMod 18)) :=
  not_isMVanishingFamily_sumAddMulProd_one_nine_mul (u := 2) (by decide) (by decide)

-- Check the three start residues and all nine length residues, including zero.
example : ∀ (s : Fin 3) (l : Fin 9),
    sumAddMulProdFamily (1 : ZMod 9) (l : ℕ)
      (fun i => ((if (s.val + i.val) % 3 = 2 then 7 else 4 : ℤ) : ZMod 9)) ≠ 0 := by
  decide
