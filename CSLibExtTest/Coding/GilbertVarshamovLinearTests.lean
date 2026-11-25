/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.GilbertVarshamovLinear
public import Mathlib.Algebra.Field.ZMod

/-! # Tests for the linear Gilbert–Varshamov bound -/

namespace Cslib.CodingTheory.GilbertVarshamovLinearTests

open Cslib.CodingTheory GilbertVarshamov LinearCode Module

-- Binary, `n = 3`, `d = 3`, `k = 0`: `1 · (1 + 3 + 3) = 7 < 8` gives a `[3, 1, ≥ 3]` code
-- (the repetition code).
example : ∃ C : LinearCode (ZMod 2) (Fin 3), finrank (ZMod 2) C = 1 ∧ (3 : ℕ∞) ≤ C.minDist :=
  exists_linearCode_finrank_eq (d := 3) (by norm_num) 0 (by decide)

-- Ternary, `n = 4`, `d = 2`, `k = 2`: `9 · (1 + 4 · 2) = 81` is not less than `81`, but
-- `k = 1` works: `3 · 9 = 27 < 81`, giving a `[4, 2, ≥ 2]` ternary code.
example : ∃ C : LinearCode (ZMod 3) (Fin 4), finrank (ZMod 3) C = 2 ∧ (2 : ℕ∞) ≤ C.minDist :=
  exists_linearCode_finrank_eq (d := 2) (by norm_num) 1 (by decide)

end Cslib.CodingTheory.GilbertVarshamovLinearTests
