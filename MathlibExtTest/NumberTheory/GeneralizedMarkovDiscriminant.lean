/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovDiscriminant

open MetaMathlibExt

-- At the even lower endpoint, 5 exceeds the half-size bound and divides neither factor.
example : ¬ (5 : ℤ) ∣ (4 : ℤ) ^ 2 - 4 :=
  not_dvd_sq_sub_four_of_large_prime (k := 4) (p := 5) (by decide) (by decide)
    (Or.inl ⟨by decide, ⟨2, rfl⟩, by decide⟩)

-- The least odd k gives a negative discriminant.
example : ¬ (5 : ℤ) ∣ -3 :=
  not_dvd_sq_sub_four_of_large_prime (k := 1) (p := 5) (by decide) (by decide)
    (Or.inr ⟨⟨0, rfl⟩, by decide⟩)
