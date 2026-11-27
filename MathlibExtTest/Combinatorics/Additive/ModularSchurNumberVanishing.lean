/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ModularSchurNumberVanishing

/-! # Tests for vanishing of modular Schur numbers -/

open MetaMathlibExt

-- Modulus one forces vanishing for every positive number of colors and summands.
example (k l : ℕ) (hk : 0 < k) (hl : 0 < l) : modularSchurNumber 1 k l = 0 :=
  (modularSchurNumber_eq_zero_iff 1 k l (by decide) hk hl).mpr (by simp [Nat.ModEq, Nat.mod_one])

-- The obstruction applies even when the number of summands is not literally one.
example : modularSchurNumber 5 3 6 = 0 :=
  (modularSchurNumber_eq_zero_iff 5 3 6 (by decide) (by decide) (by decide)).mpr (by decide)

-- Outside that residue class a positive length is admissible with just one color.
example : 0 < modularSchurNumber 5 1 2 :=
  Nat.pos_of_ne_zero fun hz =>
    (by decide : ¬ 2 ≡ 1 [MOD 5])
      ((modularSchurNumber_eq_zero_iff 5 1 2 (by decide) (by decide) (by decide)).mp hz)
