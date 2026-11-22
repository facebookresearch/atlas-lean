/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.PlanarShooting.LogisticProfile

@[expose] public section

open MathlibExt.Biology.Dynamics.FisherKPP

namespace MathlibExtTest.Biology.Dynamics.FisherKPP

/-- The constant `0` is a wave profile of every speed (it is not a front). -/
example (D r c : ℝ) : IsWaveProfile D r c (fun _ => 0) (fun _ => 0) := fun z =>
  ⟨hasDerivAt_const z 0, by simpa using hasDerivAt_const z (0 : ℝ)⟩

/-- Junk value outside the domain: with `D = 0` the profile equation, solved for `U''`, divides by
zero, so `IsWaveProfile 0 r c` only says `U'' = 0`; every theorem assumes `D > 0`. -/
example (r c : ℝ) : IsWaveProfile 0 r c (fun z => z) (fun _ => 1) := fun z =>
  ⟨hasDerivAt_id z, by simpa using hasDerivAt_const z (1 : ℝ)⟩

end MathlibExtTest.Biology.Dynamics.FisherKPP
