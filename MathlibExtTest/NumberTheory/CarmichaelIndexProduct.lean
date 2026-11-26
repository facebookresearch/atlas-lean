/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CarmichaelIndexProduct

open MetaMathlibExt

-- For a prime power, the quotient is one and the second gcd argument is zero.
example : Nat.card {u : (ZMod 4)ˣ // orderOf u ∣ 1} = 1 := by
  have h := carmichaelIndex_eq_prod 4 (hn := by decide)
  rw [show (4 : ℕ).primeFactors = {2} by decide +kernel, Finset.prod_singleton,
    show (4 : ℕ).factorization 2 = 2 by decide +kernel] at h
  change carmichaelIndex 4 = Nat.card {u : (ZMod 4)ˣ // orderOf u ∣ 1} + 1 at h
  rw [carmichaelIndex_four_and_sixtySix.1] at h
  omega

-- A modulus with two prime factors, one of them repeated, has two local counts.
example :
    (Nat.card {u : (ZMod 9)ˣ // orderOf u ∣ 2} + 1) *
      (Nat.card {u : (ZMod 5)ˣ // orderOf u ∣ 4} + 1) = 15 := by
  have h := carmichaelIndex_eq_prod 45 (hn := by decide)
  rw [show (45 : ℕ).primeFactors = {3, 5} by decide +kernel,
    Finset.prod_insert (by decide : 3 ∉ ({5} : Finset ℕ)), Finset.prod_singleton,
    show (45 : ℕ).factorization 3 = 2 by decide +kernel,
    show (45 : ℕ).factorization 5 = 1 by decide +kernel] at h
  exact h.symm.trans (show carmichaelIndex 45 = 15 by decide +kernel)
