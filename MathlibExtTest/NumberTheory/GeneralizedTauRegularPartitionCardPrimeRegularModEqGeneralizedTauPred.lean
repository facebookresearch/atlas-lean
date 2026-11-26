/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTauRegularPartitionCardPrimeRegularModEqGeneralizedTauPred

namespace MathlibExtTest.NumberTheory.GeneralizedTauRegularPartitionCardPrimeRegularModEqGeneralizedTauPred

open MetaMathlibExt

-- At `p = 2`, `n = 1`: the only partition of `1` is `1`-regular, so `τ_1(2)` is odd.
example : generalizedTau 1 2 ≡ 1 [ZMOD 2] := by
  have hcard : (Nat.Partition.restricted 1 (¬ 2 ∣ ·)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext x
    simp [Nat.Partition.restricted, Subsingleton.elim x default]
  have h := card_prime_regular_modEq_generalizedTau_pred 2 (by decide) 1
  rw [hcard] at h
  simpa using h.symm

end MathlibExtTest.NumberTheory.GeneralizedTauRegularPartitionCardPrimeRegularModEqGeneralizedTauPred
