/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.Absorption.Limit

/-! Tests: gut and central limits through the APIs. -/

namespace MathlibExtTest.Biology.Biophysics.Absorption.Limit

open MathlibExt.Biology.Biophysics.Absorption.Limit
open Filter Topology

/-- Gut amount with `D = 10`, `ka = 2`. -/
example : Filter.Tendsto (fun t => 10 * Real.exp (-2 * t)) Filter.atTop (𝓝 0) :=
  gut_amount_tendsto (by norm_num) (by norm_num)

/-- Zero dose: identically zero, still tends to zero. -/
example : Filter.Tendsto (fun t => (0:ℝ) * Real.exp (-2 * t)) Filter.atTop (𝓝 0) :=
  gut_amount_tendsto (le_refl 0) (by norm_num)

end MathlibExtTest.Biology.Biophysics.Absorption.Limit
