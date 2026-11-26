/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KGeneralizedFibonacciDiscriminant

open MetaMathlibExt

-- Exercise the production import and the original named arguments at the first allowed order.
example (F : ℤ → ℤ) (hzero : ∀ t : ℤ, 2 - (101 : ℤ) ≤ t → t < 1 → F t = 0)
    (hone : F 1 = 1)
    (hrec : ∀ t : ℤ, 1 < t → F t = ∑ i ∈ Finset.range 101, F (t - 1 - (i : ℤ)))
    (n : ℕ)
    (heq : F n * ((101 : ℤ) - 1) ^ 2 = 2 ^ (101 + 1 : ℕ) * (101 : ℤ) ^ (101 : ℕ) -
      ((101 : ℤ) + 1) ^ (101 + 1 : ℕ)) :
    (101 : ℝ) + 1.99 + (101 * Real.log 101 - 2 * Real.log ((101 : ℝ) - 1)) / Real.log 2 <
        (n : ℝ) ∧
      (n : ℝ) < 101 + 3.01 + (101 * Real.log 101 - 2 * Real.log ((101 : ℝ) - 1)) / Real.log 2 :=
  kGeneralizedFibonacci_discr_eq_index_bounds (k := 101) (hk := by decide) (F := F)
    (hFzero := hzero) (hFone := hone) (hFrec := hrec) (n := n) (h7 := heq)
