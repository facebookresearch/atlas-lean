/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.IdealAMEnvelope

@[expose] public section

open PhyslibExt.Communications.IdealAMEnvelope

namespace PhyslibExtTest.Communications.IdealAMEnvelope

/-- Exact message recovery in the non-overmodulated regime,
applied to the observation itself. -/
example (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 2 1 (envelopeObservation N 2 1 (fun _ => 1 / 2) k j) = 1 / 2 :=
  envelopeDetector_eq_message N 2 1 (1 / 2) (fun _ => 1 / 2) k _
    (fun _ => rfl) (by norm_num) (fun _ => by norm_num) (by norm_num) j

end PhyslibExtTest.Communications.IdealAMEnvelope
