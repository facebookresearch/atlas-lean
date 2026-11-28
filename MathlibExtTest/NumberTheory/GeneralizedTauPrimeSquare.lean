/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTauPrimeSquare

open MetaMathlibExt

-- At degree zero only (0, 0) contributes, so the shifted tau coefficient has residue one.
example (p : ℕ) (hp : p.Prime) (hodd : Odd p) : generalizedTau (p ^ 2 + 1) 1 ≡ 1 [ZMOD p] := by
  simpa [pentagonal_def] using generalizedTau_prime_sq_add_one_succ_modEq p hp hodd 0

-- At degree 18 for p = 3 only (0, -1) contributes, giving sign -1 from the dilated factor.
example : generalizedTau 10 19 ≡ -1 [ZMOD 3] := by
  have h := generalizedTau_prime_sq_add_one_succ_modEq 3 (by decide) (by decide) 18
  refine h.trans ?_
  simp only [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, pentagonal_def]
  decide
