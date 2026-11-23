/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ModularSchurNumbers

/-! # Tests for modular Schur numbers modulo a prime power -/

open MetaMathlibExt

-- At the color threshold, the range includes a nonunit residue (2 modulo 4).
example : modularSchurNumber 4 3 2 = 3 :=
  modularSchurNumber_prime_pow_eq 2 2 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- Extra colors may be empty.
example : modularSchurNumber 9 10 3 = 8 :=
  modularSchurNumber_prime_pow_eq 3 2 10 3 (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- When the arity is 1 modulo the prime, three copies of 2 already obstruct a partition.
example : ¬ HasSumFreePartitionMod 4 3 3 2 := by
  rintro ⟨c, hc⟩
  apply hc (c 2) (fun _ => 2) _ 2 _ (by decide)
  · exact fun _ => ⟨2, by decide, le_rfl, rfl, rfl⟩
  · exact ⟨2, by decide, le_rfl, rfl, rfl⟩
