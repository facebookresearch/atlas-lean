/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressions

/-! # Tests for available integers modulo two primes -/

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- For the primes 2 and 3 with residues 1 and 2, the integer 5 lies in both classes.
example : residueHitCount ![2, 3] ![1, 2] 5 = 2 := by decide

-- It is the only integer in `[1, 6]` that is not available.
example : availableCount ![2, 3] ![1, 2] = 5 := by decide

-- The theorem gives the determinant `2 * 3 - 1` for every choice of residues.
example (r : Fin 2 → ℕ) : (availableCount ![2, 3] r : ℤ) = 5 := by
  rw [availableCount_two_primes 2 3 Nat.prime_two Nat.prime_three (by decide) r]
  exact (Matrix.det_fin_two (R := ℤ)
    (fun i j => if i = j then ((![2, 3] i : ℕ) : ℤ) else 1)).trans (by decide)

-- Residues may exceed their moduli; direct evaluation agrees with `5 * 7 - 1`.
example : availableCount ![5, 7] ![12, 100] = 34 := by decide

example : (availableCount ![5, 7] ![12, 100] : ℤ) = 34 := by
  rw [availableCount_two_primes 5 7 Nat.prime_five Nat.prime_seven (by decide)]
  exact (Matrix.det_fin_two (R := ℤ)
    (fun i j => if i = j then ((![5, 7] i : ℕ) : ℤ) else 1)).trans (by decide)

-- The primes must be distinct: for `p = q = 2` and residues `0, 0`, only the odd integers `1`
-- and `3` are available, while the determinant is `2 * 2 - 1 = 3`.
example : availableCount ![2, 2] ![0, 0] = 2 := by decide

example : (availableCount ![2, 2] ![0, 0] : ℤ) ≠ onesDiagDet ![2, 2] := by
  have hdet : onesDiagDet ![2, 2] = 3 :=
    (Matrix.det_fin_two (R := ℤ)
      (fun i j => if i = j then ((![2, 2] i : ℕ) : ℤ) else 1)).trans (by decide)
  rw [show availableCount ![2, 2] ![0, 0] = 2 by decide, hdet]
  decide

-- With residues `0, 1` the two classes are disjoint, and all four integers are available.
example : availableCount ![2, 2] ![0, 1] = 4 := by decide

-- With no moduli, the empty product makes `1` the only candidate, and it is available; the empty
-- determinant is also `1`.
example : availableCount (k := 0) ![] ![] = 1 := by decide

example : onesDiagDet (k := 0) ![] = 1 := Matrix.det_isEmpty

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
