/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovMixing

open MathlibExt.Probability.MarkovMixing

-- Spin signs.
example : sgn true = 1 := sgn_true
example : sgn false = -1 := sgn_false

-- Total variation distance vanishes on the diagonal and is symmetric.
example (μ : Fin 3 → ℝ) : tvDist μ μ = 0 := tvDist_self μ
example (μ ν : Fin 3 → ℝ) : tvDist μ ν = tvDist ν μ := tvDist_comm μ ν

-- A chain on one state is mixed at time `0` for the unit mass.
example : IsMixedAt (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) 0 := by
  intro x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  norm_num [tvDist, Matrix.one_apply]

-- The torus step wraps around: in `ℤ_3`, the step up from `2` is `0`.
example : stepUp (d := 1) (n := 3) 0 (fun _ => 2) = fun _ => 0 := by
  decide
