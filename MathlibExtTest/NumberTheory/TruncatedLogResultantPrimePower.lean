/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TruncatedLogResultantPrimePower

open MetaMathlibExt

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 5 :=
  not_dvd_truncatedLogResultantProduct_of_prime_power (p := 5) (e := 1)
    (hp := by decide) (hp4 := by decide) (he := by decide)

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 25 :=
  not_dvd_truncatedLogResultantProduct_of_prime_power (p := 5) (e := 2)
    (hp := by decide) (hp4 := by decide) (he := by decide)

-- The even-power theorem also applies to primes congruent to 3 modulo 4.
example : ¬ (3 : ℤ) ∣ truncatedLogResultantProduct 9 :=
  not_dvd_truncatedLogResultantProduct_of_even_power (p := 3) (e := 1)
    (hp := by decide) (hp2 := by decide) (he := by decide)

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 625 :=
  not_dvd_truncatedLogResultantProduct_of_even_power (p := 5) (e := 2)
    (hp := by decide) (hp2 := by decide) (he := by decide)
