/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete

/-!
# Canonical complexity integration checks

The shared API reuses the existing machine-level SAT and 3SAT proofs, without
changing their complexity model or deriving class membership from declared costs.
-/

@[expose] public section

namespace Cslib.Complexity.IntegrationTests

open Cslib.Complexity Cslib.CookLevin

example : NPComplete satDec :=
  npComplete_iff.mpr Cslib.Complexity.SatVerifier.Machine.cook_levin_SAT_np_complete

example : NPHard Cslib.Complexity.Karp.sat3Dec :=
  NPHard.of_polyManyOneRed
    Cslib.Complexity.SatVerifier.Machine.cook_levin_SAT_np_complete.2
    Cslib.Complexity.Karp.satDec_polyManyOneRed_sat3Dec

end Cslib.Complexity.IntegrationTests
