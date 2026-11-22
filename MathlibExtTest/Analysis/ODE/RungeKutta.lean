/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.RungeKutta

open MathlibExt.Analysis.ODE.RungeKutta
open Filter Topology

-- Euler is explicit Euler.
example (f : ℝ → ℝ → ℝ) (t y h : ℝ) : rkStep eulerRK f t y h = y + h • f t y :=
  euler_step f t y h

-- The order conditions hold for the textbook methods.
example : OrderOne eulerRK := eulerRK_orderOne

example : OrderTwo midpointRK := midpointRK_orderTwo

example : OrderTwo heunRK := heunRK_orderTwo

example : OrderFour rk4 := rk4_orderFour

-- RK4 on `y' = y`: one step multiplies by the stability polynomial at `z = h`.
example (y h : ℝ) :
    rkStep rk4 (fun _ y => (1 : ℝ) * y) 0 y h =
      y * (1 + 1 * h + (1 * h) ^ 2 / 2 + (1 * h) ^ 3 / 6 + (1 * h) ^ 4 / 24) :=
  rk4_stability 1 y h

-- Consistency of Euler on `y' = y` at `(0, 1)`: the difference quotient tends to `1`.
example : Tendsto (fun h => h⁻¹ • (rkStep eulerRK (fun _ y => y) 0 1 h - 1))
    (𝓝[≠] 0) (𝓝 (1 : ℝ)) :=
  rkStep_sub_inv_smul_tendsto eulerRK (fun _ y => y) 0 1 eulerRK_orderOne
    (by show ContinuousAt Prod.snd (0, 1); exact continuous_snd.continuousAt)
