/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NonSecondPentagonal

open MetaMathlibExt

private theorem sqrt_eq_of_bounds {m k : ℕ} (hl : k ^ 2 ≤ m) (hu : m < (k + 1) ^ 2) :
    Nat.sqrt m = k :=
  le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr hu)) (Nat.le_sqrt'.mpr hl)

-- The first term is positive, and s = 0 there.
example : nthNonValue (fun j => (3 * j ^ 2 + j) / 2) 1 = 1 := by
  simpa using nthNonValue_secondPentagonal (n := 1) (hn := by decide)

-- The square root jumps from 1 to 2 at n = 6, skipping the excluded value 7.
example : nthNonValue (fun j => (3 * j ^ 2 + j) / 2) 5 = 6 := by
  have hs : Nat.sqrt (2 * 5 / 3) = 1 := sqrt_eq_of_bounds (by decide) (by decide)
  simpa [hs] using nthNonValue_secondPentagonal (n := 5) (hn := by decide)

example : nthNonValue (fun j => (3 * j ^ 2 + j) / 2) 6 = 8 := by
  have hs : Nat.sqrt (2 * 6 / 3) = 2 := sqrt_eq_of_bounds (by decide) (by decide)
  simpa [hs] using nthNonValue_secondPentagonal (n := 6) (hn := by decide)

-- For s = 4, the cut is 2n = 72. Check below, at, and above it with s still fixed.
example : nthNonValue (fun j => (3 * j ^ 2 + j) / 2) 35 = 39 := by
  have hs : Nat.sqrt (2 * 35 / 3) = 4 := sqrt_eq_of_bounds (by decide) (by decide)
  simpa [hs] using nthNonValue_secondPentagonal (n := 35) (hn := by decide)

example : nthNonValue (fun j => (3 * j ^ 2 + j) / 2) 36 = 41 := by
  have hs : Nat.sqrt (2 * 36 / 3) = 4 := sqrt_eq_of_bounds (by decide) (by decide)
  simpa [hs] using nthNonValue_secondPentagonal (n := 36) (hn := by decide)

example : nthNonValue (fun j => (3 * j ^ 2 + j) / 2) 37 = 42 := by
  have hs : Nat.sqrt (2 * 37 / 3) = 4 := sqrt_eq_of_bounds (by decide) (by decide)
  simpa [hs] using nthNonValue_secondPentagonal (n := 37) (hn := by decide)
