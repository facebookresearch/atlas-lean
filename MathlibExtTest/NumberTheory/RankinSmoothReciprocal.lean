/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RankinSmoothReciprocal
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.RankinSmoothReciprocalTest

-- The smallest allowed smoothness bound includes powers of 2. Take `s = 1/2`.
example :
    ∑' n : {n : ℕ // n ∈ Nat.smoothNumbers 3 ∧ (4 : ℝ) < n}, (1 : ℝ) / n ≤
      (4 : ℝ) ^ (-(1 / 2 : ℝ)) * ∑' n : Nat.smoothNumbers 3,
        (n : ℝ) ^ (-(1 - 1 / 2 : ℝ)) := by
  have hfloor : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
  have h := smoothReciprocalTail_le_rpow_mul_smoothZeta (x := 4) (y := 2) (s := 1 / 2)
    le_rfl (by norm_num) (by norm_num) (by norm_num)
  rwa [hfloor] at h

-- A nonintegral bound between 3 and 4 has strict Mathlib cutoff 4, for any admissible `s`.
example {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∑' n : {n : ℕ // n ∈ Nat.smoothNumbers 4 ∧ (6 : ℝ) < n}, (1 : ℝ) / n ≤
      (6 : ℝ) ^ (-s) * ∑' n : Nat.smoothNumbers 4, (n : ℝ) ^ (-(1 - s)) := by
  have hfloor : ⌊(7 / 2 : ℝ)⌋₊ = 3 :=
    (Nat.floor_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩
  have h := smoothReciprocalTail_le_rpow_mul_smoothZeta (x := 6) (y := 7 / 2)
    (by norm_num) (by norm_num) hs0 hs1
  rwa [hfloor] at h

-- At `y = 2`, the zeta sum includes 1; the tail at `x = 4` excludes 4 and includes 8.
example : (1 : ℕ) ∈ Nat.smoothNumbers 3 ∧
    (4 : ℕ) ∉ {n : ℕ | n ∈ Nat.smoothNumbers 3 ∧ (4 : ℝ) < n} ∧
    (8 : ℕ) ∈ {n : ℕ | n ∈ Nat.smoothNumbers 3 ∧ (4 : ℝ) < n} := by
  have h1 : (1 : ℕ) ∈ Nat.smoothNumbers 2 := Nat.mem_smoothNumbers_of_lt (by decide) (by decide)
  have h8 : (8 : ℕ) ∈ Nat.smoothNumbers 3 :=
    Nat.pow_mul_mem_smoothNumbers (p := 2) (by decide) 3 h1
  exact ⟨Nat.smoothNumbers_mono (by decide) h1, fun h ↦ lt_irrefl (4 : ℝ) h.2, h8, by norm_num⟩

end MetaMathlibExt.RankinSmoothReciprocalTest
