/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PalapiesTriangularArrays

open MetaMathlibExt MetaMathlibExt.TriangularRecurrence

-- Row zero is the empty product, even if the first factor has zero constant term.
example (α α' γ' : ℤ) :
    (PowerSeries.mk fun k : ℕ => negPos ⟨α, 0, 0, α', 0, γ'⟩ 0 k) = 1 := by
  simpa using negPos_egf_beta_zero α 0 α' γ' 0

-- The coefficient of degree three in the binomial row (1 + X)⁻².
example : negPos ⟨0, 0, 1, 0, 0, 1⟩ (-2) 3 = -4 := by
  change negPosAux _ 1 3 = -4
  norm_num [negPosAux.eq_1, negPosAux.eq_2, negPosAux.eq_3, negPosAux.eq_4, weight, weight']

-- The factor at j = 1 is X. Its vanishing constant term kills even row -3.
example :
    (PowerSeries.mk fun k : ℕ => negPos ⟨1, 0, 1, 0, 0, 1⟩ (-3) k) = 0 := by
  rw [show (-3 : ℤ) = -(3 : ℕ) by rfl, negPos_egf_beta_zero]
  apply PowerSeries.inv_eq_zero.mpr
  simp [Finset.prod_range_succ]

-- Reflection of the binomial array gives the same coefficient on the other side of the diagonal.
example : negNeg ⟨0, 0, 1, 0, 0, 1⟩ (-2) (-5) = -4 := by
  change negNegAux _ 1 3 = -4
  norm_num [negNegAux.eq_1, negNegAux.eq_2, negNegAux.eq_3, negNegAux.eq_4, weight, weight']

-- With unequal coefficients and nonzero constant term, the dual entry is in row 3, column 1.
example : negNeg ⟨2, -1, 3, 0, 0, 1⟩ (-2) (-4) = 48 := by
  rw [negNeg_duality 2 (-1) 3 2 4]
  change array _ 3 1 = 48
  norm_num [array]

-- Column -1 of the negative triangle reflects to row zero of the ordinary array.
example (α β γ : ℤ) (p : ℕ) :
    negNeg ⟨α, β, γ, 0, 0, 1⟩ (.negSucc p) (-1) = if p = 0 then 1 else 0 := by
  rw [Int.negSucc_eq, negNeg_duality α β γ (p + 1) 1]
  simp [negNeg]
