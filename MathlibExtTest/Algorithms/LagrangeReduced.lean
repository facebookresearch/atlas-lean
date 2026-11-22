/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.LagrangeReduced
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Algorithms.LagrangeReduced

/-- `u = (1, 0)` and `v = (1/2, 1)` form a Lagrange-reduced pair with nonzero cross term
`u ⬝ᵥ v = 1/2`: `|u ⬝ᵥ v| = (u ⬝ᵥ u) / 2` and `u ⬝ᵥ u = 1 ≤ 5/4 = v ⬝ᵥ v`. The bound
applies to the combination `-u + v = (-1/2, 1)` (`a = -1`, `b = 1`), whose squared length
is `5/4`. -/
example : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] ≤ (4 / 3) *
    ((fun i => ((-1 : ℤ) : ℝ) * (![1, 0] : Fin 2 → ℝ) i + ((1 : ℤ) : ℝ) * ![1 / 2, 1] i) ⬝ᵥ
      (fun i => ((-1 : ℤ) : ℝ) * (![1, 0] : Fin 2 → ℝ) i + ((1 : ℤ) : ℝ) * ![1 / 2, 1] i)) :=
  lagrange_short ![1, 0] ![1 / 2, 1]
    (by norm_num [dotProduct, Fin.sum_univ_two])
    (by norm_num [dotProduct, Fin.sum_univ_two])
    (by norm_num [dotProduct, Fin.sum_univ_two])
    (-1) 1 (by decide)

end
