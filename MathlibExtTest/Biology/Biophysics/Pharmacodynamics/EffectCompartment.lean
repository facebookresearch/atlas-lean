/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.Pharmacodynamics.EffectCompartment

/-! Tests: initial effect value. -/

namespace MathlibExtTest.Biology.Biophysics.Pharmacodynamics.EffectCompartment

open MathlibExt.Biology.Biophysics.Pharmacodynamics.EffectCompartment

/-- Initial effect at unit lag rate. -/
example : effectConc 1 2 (fun s => s) 0 = 2 :=
  effectConc_zero 1 2 _

/-- Constant unit input gives a nonnegative effect at time `2`. -/
example : 0 ≤ effectConc 1 0 (fun _ => 1) 2 :=
  effectConc_nonneg (by norm_num) le_rfl (by norm_num) (fun s _ => zero_le_one)

/-- The lag equation at time `2` for constant input. -/
example : HasDerivAt (effectConc 1 0 (fun _ => (1:ℝ)))
    (1 * (1 - effectConc 1 0 (fun _ => (1:ℝ)) 2)) 2 :=
  hasDerivAt_effectConc (fun a b => intervalIntegrable_const) continuousAt_const

end MathlibExtTest.Biology.Biophysics.Pharmacodynamics.EffectCompartment
