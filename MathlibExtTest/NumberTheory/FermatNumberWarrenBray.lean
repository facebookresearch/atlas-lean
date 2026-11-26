/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.FermatNumberWarrenBray

/-! # Tests for the Warren–Bray congruence for Fermat numbers -/

open MetaMathlibExt

-- The least index covered by the theorem, with p = F₂.
example : 2 ^ ((17 - 1) / 2) ≡ 1 [MOD Nat.fermatNumber 2] :=
  two_pow_half_modEq_one_fermatNumber (n := 2) (p := 17) le_rfl
    (by decide) (by decide) (by decide)

-- The modulus is the whole of F₅, not its proper prime factor 641.
example : 2 ^ ((641 - 1) / 2) ≡ 1 [MOD Nat.fermatNumber 5] :=
  two_pow_half_modEq_one_fermatNumber (n := 5) (p := 641) (by decide)
    (by norm_num) (by decide) (by decide)

-- The same statement fails one index below the theorem's range, with p = F₁.
example : ¬ 2 ^ ((5 - 1) / 2) ≡ 1 [MOD Nat.fermatNumber 1] := by decide
