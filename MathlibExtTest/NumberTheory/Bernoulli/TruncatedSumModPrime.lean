/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime

namespace MetaMathlibExt.sum_bernoulli_to_prime_sub_three_mod_prime

open Finset

-- At the first allowed prime the sum includes exactly the terms through B₂.
private lemma sum_at_five : ∑ j ∈ range (5 - 2), bernoulli j = 2 / 3 := by
  norm_num [sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two]

example : ¬5 ∣ (2 / 3 : ℚ).den ∧ ratResidue 5 (2 / 3) = 4 := by
  have h := sum_bernoulli_to_prime_sub_three_mod_prime 5 (by decide) (by decide)
  rw [sum_at_five] at h
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [ratResidue]
  decide

-- For the excluded odd prime 3 the sum consists of B₀ alone.
example : ratResidue 3 (∑ j ∈ range (3 - 2), bernoulli j) ≠ ratResidue 3 (-1) := by
  rw [show 3 - 2 = 1 by decide, sum_range_one, bernoulli_zero]
  norm_num [ratResidue]
  decide

end MetaMathlibExt.sum_bernoulli_to_prime_sub_three_mod_prime
