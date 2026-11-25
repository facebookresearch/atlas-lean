/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyNumerator

open Finset MathlibExt.NumberTheory.FareyNumeratorWanted

-- Both endpoints occur in this Farey sequence. Only the denominator of 1/2 is counted.
example : ((Icc 1 5).filter (fun b => Nat.Coprime 1 b ∧
    (1 : ℚ) / 3 < 1 / b ∧ (1 : ℚ) / b ≤ 1 / 2)) = {2} := by
  decide +kernel

-- At the minimum order for k = 2 and h = 8, the strict mediant cut keeps 8/13 and 8/15.
example : ((Icc 1 15).filter (fun b => Nat.Coprime 8 b ∧
    (1 : ℚ) / 2 < 8 / b ∧ (8 : ℚ) / b < 2 / 3)) = {13, 15} := by
  decide +kernel

example : 2 * ((Icc 1 15).filter (fun b => Nat.Coprime 8 b ∧
    (1 : ℚ) / 2 < 8 / b ∧ (8 : ℚ) / b < 2 / 3)).card = 4 := by
  have hφ : Nat.totient 8 = 4 := by decide +kernel
  simpa only [Nat.cast_ofNat, show (2 : ℚ) * 2 - 1 = 3 by decide +kernel, hφ] using
    (farey_between_count 2 15 8 (by decide) (by decide) (by decide)).2 (by decide)
