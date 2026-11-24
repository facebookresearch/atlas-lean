/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddPrimeDeficientPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- The theorem includes the zero exponent.
example : ¬ IsKLDeficientPerfect 0 1 3 :=
  not_isKLDeficientPerfect_of_prime_odd (k := 0) (l := 1) (p := 3)
    (hp := by decide) (hpo := ⟨1, rfl⟩)

example : ¬ IsKLDeficientPerfect 2 3 5 :=
  not_isKLDeficientPerfect_of_prime_odd (k := 2) (l := 3) (p := 5)
    (hp := by decide) (hpo := ⟨2, rfl⟩)

-- The prime two satisfies the predicate, so the oddness hypothesis matters.
example : IsKLDeficientPerfect 2 1 2 := by
  refine ⟨1, ?_⟩
  unfold KLDeficientPerfectWith
  decide
