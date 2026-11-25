/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PalapiesTriangularArraysReflection

open MetaMathlibExt MetaMathlibExt.TriangularRecurrence

-- At positive rows, reflection reverses the columns of the ordinary array.
example : (reflect ⟨1, 1, 2, 2, -1, 3⟩).negPos 2 0 = 20 := by
  rw [(reflect_negPos_eq_negNeg _).1]
  change array ⟨1, 1, 2, 2, -1, 3⟩ 2 2 = 20
  norm_num [array]

-- At row -2, column 1 reflects to offset 1 below the negative diagonal.
example : (reflect ⟨1, 1, 2, 2, -1, 3⟩).negPos (-2) 1 = 1 / 36 := by
  rw [(reflect_negPos_eq_negNeg _).1]
  change negNegAux ⟨1, 1, 2, 2, -1, 3⟩ 1 1 = 1 / 36
  norm_num [negNegAux.eq_1, negNegAux.eq_2, negNegAux.eq_3, negNegAux.eq_4, weight, weight']

-- Reflection preserves the zero quotient when the denominator vanishes but the numerator does not.
example : (reflect ⟨0, -1, 1, 0, 0, 1⟩).negNeg (-1) (-1 - 1) = 0 := by
  rw [(reflect_negPos_eq_negNeg _).2.1]
  change negPosAux ⟨0, -1, 1, 0, 0, 1⟩ 0 1 = 0
  norm_num [negPosAux.eq_1, negPosAux.eq_2, weight, weight']
