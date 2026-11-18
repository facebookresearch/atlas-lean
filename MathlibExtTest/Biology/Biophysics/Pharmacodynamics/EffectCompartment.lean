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

end MathlibExtTest.Biology.Biophysics.Pharmacodynamics.EffectCompartment
