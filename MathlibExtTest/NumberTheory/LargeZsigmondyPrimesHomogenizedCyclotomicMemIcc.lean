/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LargeZsigmondyPrimesHomogenizedCyclotomicMemIcc

/-!
# Tests for bounds on homogenized cyclotomic values

Concrete bounds and a positivity corollary of the homogenized cyclotomic bounds.
-/

namespace MathlibExtTest.NumberTheory.LargeZsigmondyPrimesHomogenizedCyclotomicMemIcc

open MetaMathlibExt

example : (3 : ℤ) ≤ homogenizedCyclotomic 1 5 2 ∧
    homogenizedCyclotomic 1 5 2 ≤ 7 := by
  simpa using homogenizedCyclotomic_mem_Icc (a := 5) (b := 2) (n := 1)
    (by decide) (by decide) (by decide)

example : (3 : ℤ) ≤ homogenizedCyclotomic 2 5 2 ∧
    homogenizedCyclotomic 2 5 2 ≤ 7 := by
  simpa using homogenizedCyclotomic_mem_Icc (a := 5) (b := 2) (n := 2)
    (by decide) (by decide) (by decide)

example : (9 : ℤ) ≤ homogenizedCyclotomic 6 5 2 ∧
    homogenizedCyclotomic 6 5 2 ≤ 49 := by
  have ht : Nat.totient 6 = 2 := by decide
  simpa [ht] using homogenizedCyclotomic_mem_Icc (a := 5) (b := 2) (n := 6)
    (by decide) (by decide) (by decide)

example {a b n : ℕ} (hb : 0 < b) (hba : b < a) (hn : 0 < n) :
    0 < homogenizedCyclotomic n a b := by
  have hdiff : (0 : ℤ) < (a : ℤ) - b := sub_pos.mpr (by exact_mod_cast hba)
  exact (pow_pos hdiff _).trans_le (homogenizedCyclotomic_mem_Icc hb hba hn).1

end MathlibExtTest.NumberTheory.LargeZsigmondyPrimesHomogenizedCyclotomicMemIcc
