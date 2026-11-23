/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
`Theorems/Thm_Polynomial_aeval_pow_card_eq_pow_card.lean` and
`P2M/Sol/S_Polynomial_aeval_pow_card_eq_pow_card.lean`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib (https://github.com/leanprover-community/mathlib4):
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Evaluation and the Frobenius power over finite fields

Evaluating a polynomial at a `q`-th power is the `q`-th power of the
evaluation, for `q` the cardinality of a finite field: expand the polynomial
and use that expansion by `q` is the `q`-th power.
-/

@[expose] public section

/-- Evaluating `p` at `x ^ q` equals the `q`-th power of evaluating `p` at
`x`, where `q` is the cardinality of the finite field `F`. -/
theorem Polynomial.aeval_pow_card_eq_pow_card (F : Type*) [Field F] [Fintype F]
    (E : Type*) [CommRing E] [Algebra F E] (p : Polynomial F) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F := by
  rw [← Polynomial.expand_aeval (Fintype.card F) p x, FiniteField.Polynomial.expand_card,
    map_pow]
