/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EisensteinRamanujanCongruence

open PowerSeries
open scoped PowerSeries.WithPiTopology

-- At weight 12 the weight-zero factor is 1, giving the Ramanujan congruence modulo 691.
example (n : ℕ) (hn : 1 ≤ n) :
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    (((ArithmeticFunction.sigma 11 n : ℚ) - coeff n Δ) / 691).den.Coprime 691 := by
  intro Δ
  have h := (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_one 12 (by decide)).2 n hn
  have hB : (-bernoulli 12 / (2 * 12)).num.natAbs = 691 := by decide +kernel
  have hunit : PowerSeries.mk (fun j => if j = 0 then (1 : ℚ) else 0) = 1 := by
    ext j
    simp [coeff_one]
  simpa [show n ≠ 0 by omega, hunit, hB, Nat.sup_divisors_id, Δ] using h
