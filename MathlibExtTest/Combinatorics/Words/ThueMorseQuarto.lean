/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.ThueMorseQuarto

open MetaMathlibExt

-- Compare the two bits at zero and on either side of two binary-length changes.
example : [0, 31, 32, 63, 64].map (fun n => (thueMorseQuarto n, thueMorse n)) =
    [(false, false), (true, true), (false, true), (true, false), (true, true)] := by
  decide +kernel

-- A power of two has a single set bit, so the quarto bit is zero at odd exponents.
example (k : ℕ) : thueMorseQuarto (2 ^ (2 * k + 1)) = false := by
  have digits (j : ℕ) : Nat.digits 2 (2 ^ j) = List.replicate j 0 ++ [1] := by
    simpa using Nat.digits_base_pow_mul (b := 2) (k := j) (m := 1) (by decide) (by decide)
  rw [thueMorseQuarto_eq_xor, thueMorse, digits, Nat.log_pow (by decide)]
  simp [List.count_replicate]
