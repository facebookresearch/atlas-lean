/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.FermatNumberSquareFactors

/-! # Tests for squared prime factors of Fermat numbers -/

open MetaMathlibExt

-- At the initial index, 3 divides F₀, but 2² is not 1 modulo 9.
example : ¬ 3 ^ 2 ∣ Nat.fermatNumber 0 := by
  apply mt (sq_dvd_fermatNumber_iff (p := 3) (n := 0) (by decide) (by decide)).mp
  decide

-- The proper prime factor 641 of F₅ occurs only once, ruling out the congruence modulo 641².
example : ¬ 2 ^ (641 - 1) ≡ 1 [MOD 641 ^ 2] := by
  apply mt (sq_dvd_fermatNumber_iff (p := 641) (n := 5) (by norm_num) (by decide)).mpr
  decide
