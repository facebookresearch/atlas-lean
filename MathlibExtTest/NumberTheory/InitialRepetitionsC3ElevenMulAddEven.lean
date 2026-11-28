/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

meta import MathlibExt.NumberTheory.InitialRepetitionsC3
import MathlibExt.NumberTheory.InitialRepetitionsC3ElevenMulAddEven

/-! # Tests for $c_3$ on three progressions modulo eleven -/

open MetaMathlibExt

-- Count the admissible partitions directly at the first term of each progression.
#guard initialRepetitionsC3 5 == 2
#guard initialRepetitionsC3 7 == 4
#guard initialRepetitionsC3 9 == 8

-- The public theorem gives all three parities at the next terms.
example : Even (initialRepetitionsC3 16) ∧ Even (initialRepetitionsC3 18) ∧
    Even (initialRepetitionsC3 20) :=
  initialRepetitionsC3_eleven_mul_add_even 1
