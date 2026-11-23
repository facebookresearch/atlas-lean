/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_HeckeEigensystem.lean`,
`Theorems/Thm_AutomorphicForm_satakePow_add_pow.lean`
and
`P2M/Sol/S_AutomorphicForm_satakePow_add_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Ring.Basic

import Mathlib.Tactic.Ring

@[expose] public section

namespace AutomorphicForm

/-- The Satake power sum attached to parameters `s` and `e`: the sequence
starting at `2` and `s` and satisfying the second-order recurrence with
coefficients `s` and `-e` at each step. -/
def satakePow {R : Type*} [CommRing R] (n : ℕ) (s e : R) : R :=
  match n with
  | 0 => 2
  | 1 => s
  | (n + 2) => s * satakePow (n + 1) s e - e * satakePow n s e

@[simp]
public theorem satakePow_zero {R : Type*} [CommRing R] (s e : R) :
    satakePow 0 s e = 2 :=
  rfl

@[simp]
public theorem satakePow_one {R : Type*} [CommRing R] (s e : R) :
    satakePow 1 s e = s :=
  rfl

public theorem satakePow_add_two {R : Type*} [CommRing R] (n : ℕ) (s e : R) :
    satakePow (n + 2) s e = s * satakePow (n + 1) s e - e * satakePow n s e :=
  rfl

/-- For elements `α` and `β` of a commutative ring, the Satake power sum at
the sum and product parameters is the sum of the individual powers:
`satakePow n (α + β) (α * β) = α ^ n + β ^ n`. This holds for every `n`,
including the cases of repeated or zero parameters. -/
public theorem satakePow_add_pow {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, satakePow n (α + β) (α * β) = α ^ n + β ^ n := by
  have key : ∀ n : ℕ,
      satakePow n (α + β) (α * β) = α ^ n + β ^ n ∧
        satakePow (n + 1) (α + β) (α * β) = α ^ (n + 1) + β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · rw [satakePow_zero, pow_zero, pow_zero]
        norm_num
      · rw [satakePow_one, pow_one, pow_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [satakePow_add_two, ih.1, ih.2]
      ring
  exact fun n => (key n).1

end AutomorphicForm
