/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasDoublingDivisibility

open MetaMathlibExt

-- The even formula includes index zero.
example (params : LucasSequenceParams) :
    lucasU params 0 = lucasU params 0 * lucasV params 0 :=
  (lucasU_two_mul_and_lucasU_dvd params).1 0

-- The odd formula at n = 2 gives F₅ = F₂² + F₃².
example : lucasU fibonacciLucasParams 5 = 5 := by
  rw [(lucasU_two_mul_and_lucasU_dvd fibonacciLucasParams).2.1 2]
  decide

-- The divisibility clause includes both a nontrivial multiple and the zero index.
example : lucasU fibonacciLucasParams 4 ∣ lucasU fibonacciLucasParams 12 :=
  (lucasU_two_mul_and_lucasU_dvd fibonacciLucasParams).2.2 4 12 (by decide)

example (params : LucasSequenceParams) : lucasU params 0 ∣ lucasU params 0 :=
  (lucasU_two_mul_and_lucasU_dvd params).2.2 0 0 (dvd_refl 0)
