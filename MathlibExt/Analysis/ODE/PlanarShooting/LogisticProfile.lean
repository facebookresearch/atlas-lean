/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Profiles and fronts of the logistic traveling-wave ODE

These predicates specify the first-order system and its two limiting states.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Dynamics.FisherKPP

open Real Filter Topology

/-- `U` is a traveling-wave profile of speed `c` for `∂u/∂t = D ∂²u/∂x² + r u (1 - u)`: it is
twice differentiable with first derivative `U'` and `U'' = -(c U' + r U (1 - U)) / D`, which for
`D ≠ 0` is the profile equation `D U'' + c U' + r U (1 - U) = 0`. -/
def IsWaveProfile (D r c : ℝ) (U U' : ℝ → ℝ) : Prop :=
  ∀ z, HasDerivAt U (U' z) z ∧
    HasDerivAt U' ((-(c * U' z) - r * U z * (1 - U z)) / D) z

/-- A traveling front of speed `c`: a wave profile with `0 < U < 1`, `U → 1` at `-∞` and
`U → 0` at `+∞`. -/
def IsFront (D r c : ℝ) (U U' : ℝ → ℝ) : Prop :=
  IsWaveProfile D r c U U' ∧ (∀ z, 0 < U z ∧ U z < 1) ∧ Tendsto U atBot (𝓝 1) ∧
    Tendsto U atTop (𝓝 0)

end MathlibExt.Biology.Dynamics.FisherKPP
