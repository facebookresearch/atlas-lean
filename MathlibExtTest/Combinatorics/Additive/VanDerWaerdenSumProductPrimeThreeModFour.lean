/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductPrimeThreeModFour

open MetaMathlibExt
open scoped BigOperators

-- The two periodic counterexamples in Lemma 7 of Bialostocki and Oles.
private def wordSeven : Fin 5 → ZMod 7 := ![2, 3, 3, 3, 3]

private def wordEleven : Fin 3 → ZMod 11 := ![5, 3, 3]

-- Every full period contributes sum 0 and product 1, so extending a block by a full period
-- leaves its sum plus product unchanged. Check all starting residues and length remainders,
-- including remainder 0, when the value is the empty sum plus the empty product.
example : ∀ s : Fin 5,
    (∑ i : Fin 5, wordSeven (Fin.ofNat 5 (s.val + i.val))) = 0 ∧
      (∏ i : Fin 5, wordSeven (Fin.ofNat 5 (s.val + i.val))) = 1 := by
  decide +kernel

example : ∀ s l : Fin 5,
    sumAddMulProdFamily (1 : ZMod 7) l.val
      (fun i => wordSeven (Fin.ofNat 5 (s.val + i.val))) ≠ 0 := by
  decide +kernel

example : ∀ s : Fin 3,
    (∑ i : Fin 3, wordEleven (Fin.ofNat 3 (s.val + i.val))) = 0 ∧
      (∏ i : Fin 3, wordEleven (Fin.ofNat 3 (s.val + i.val))) = 1 := by
  decide +kernel

example : ∀ s l : Fin 3,
    sumAddMulProdFamily (1 : ZMod 11) l.val
      (fun i => wordEleven (Fin.ofNat 3 (s.val + i.val))) ≠ 0 := by
  decide +kernel

-- Clients at the smallest eligible prime and at a larger prime with more than one block.
example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 7)) :=
  not_isMVanishingFamily_sumAddMulProd_one_prime_three_mod_four
    (by decide) (by decide) (by decide) (by decide)

example : ¬ IsMVanishingFamily 2 (sumAddMulProdFamily (1 : ZMod 11)) :=
  not_isMVanishingFamily_sumAddMulProd_one_prime_three_mod_four
    (by decide) (by decide) (by decide) (by decide)
