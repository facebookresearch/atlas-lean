/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsFreeCount

/-! # Tests for free integers modulo two primes -/

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- The pair of zero remainders contributes the endpoint 6.
example : (Finset.Icc 1 6).filter
    (fun n => residueHitCount ![2, 3] ![1, 2] n = 0) = {4, 6} := by decide

-- The formula applies to every choice of residues, including noncanonical representatives.
example (r : Fin 2 → ℕ) : (freeCount ![2, 3] r : ℤ) = 2 := by
  rw [freeCount_two_primes 2 3 Nat.prime_two Nat.prime_three (by decide) r]
  decide

example : freeCount ![5, 7] ![12, 100] = 24 := by decide

-- Two distinct residue classes modulo the same prime can cover the entire interval.
example : freeCount ![2, 2] ![0, 1] = 0 := by decide

example : borderedOnesDiagDet ![2, 2] = 1 := by decide

-- With no moduli, the empty product leaves exactly one integer, which hits no classes.
example : freeCount (k := 0) ![] ![] = 1 := by decide

example : borderedOnesDiagDet (k := 0) ![] = 1 := by decide

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
