/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FloorNonMultiples

open MetaMathlibExt

-- At the smallest allowed modulus, the image consists of the odd numbers.
example :
    (fun n : ℕ => (2 * n - 1) / (2 - 1)) '' {n | 1 ≤ n} = {m | m % 2 = 1} := by
  rw [image_floor_eq_nonMultiples (by decide : 2 ≤ 2)]
  ext m
  simp only [Set.mem_ofPred_eq, Nat.dvd_iff_mod_eq_zero]
  omega

-- Both neighbors of the first skipped multiple occur.
example :
    let values := (fun n : ℕ => (3 * n - 1) / (3 - 1)) '' {n | 1 ≤ n}
    2 ∈ values ∧ 3 ∉ values ∧ 4 ∈ values := by
  dsimp only
  rw [image_floor_eq_nonMultiples (by decide : 2 ≤ 3)]
  simp only [Set.mem_ofPred_eq]
  decide
