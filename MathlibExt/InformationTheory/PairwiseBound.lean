/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BhattacharyyaCoeff

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bhattacharyya pairwise error bound

For nonnegative vectors `p` and `q` on a finite alphabet, the `p`-mass of the region where
`q` is at least `p` is at most their Bhattacharyya coefficient
`bhattacharyyaCoeff p q = ∑ x, √(p x * q x)`. When `p` and `q` are the output distributions of
two codewords, the left side is the probability that a maximum-likelihood decoder, given an
output drawn from `p`, scores `q` at least as high as `p`. Averaging over random codebooks is
not included here.

## Main results

* `InformationTheory.pairwise_error_le`: the `p`-mass of `{x | p x ≤ q x}` is at most
  `bhattacharyyaCoeff p q`.
-/

@[expose] public section

namespace InformationTheory

open MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

/-- **Bhattacharyya pairwise error bound.** For nonnegative vectors `p` and `q` on a finite
alphabet, the `p`-mass of the region where `q` is at least `p` is at most the Bhattacharyya
coefficient `∑ x, √(p x * q x)`. No hypothesis on `q` is needed. -/
theorem pairwise_error_le {X : Type*} [Fintype X] (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) :
    ∑ x ∈ Finset.univ.filter (fun x => p x ≤ q x), p x ≤ bhattacharyyaCoeff p q := by
  calc
    ∑ x ∈ Finset.univ.filter (fun x => p x ≤ q x), p x
        ≤ ∑ x ∈ Finset.univ.filter (fun x => p x ≤ q x), Real.sqrt (p x * q x) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hpq : p x ≤ q x := (Finset.mem_filter.mp hx).2
          calc p x = Real.sqrt (p x * p x) := (Real.sqrt_mul_self (hp0 x)).symm
            _ ≤ Real.sqrt (p x * q x) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpq (hp0 x))
    _ ≤ ∑ x, Real.sqrt (p x * q x) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Real.sqrt_nonneg _
    _ = bhattacharyyaCoeff p q := rfl

end InformationTheory

end
