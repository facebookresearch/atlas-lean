/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
state the growth bound directly for Mathlib's Catalan numbers and narrow its imports.
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # A growth bound for Catalan numbers

The bound applies to counts of finite binary trees and domination of generating-function
coefficients. It is extracted from `SparsificationLemma.Cal.stCatLe` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5).

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

/-- The `n`th Catalan number is at most `4 ^ n`. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  calc
    catalan n ≤ (n + 1) * catalan n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    _ = n.centralBinom := succ_mul_catalan_eq_centralBinom n
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n
