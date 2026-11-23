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
applied to the assumed quadrature observation itself. -/
example (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 2 1 (quadratureObservation N 2 1 (fun _ => 1 / 2) k j) = 1 / 2 :=
  envelopeDetector_eq_message_of_abs_le N 2 1 (1 / 2) (fun _ => 1 / 2) k _
    (fun _ => rfl) (by norm_num) (fun _ => by norm_num) (by norm_num) j

/-- The 100% modulation boundary `A = μ M` (`A = μ = M = 1`, message `-1`, envelope `0`)
is recovered exactly. -/
example (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (quadratureObservation N 1 1 (fun _ => -1) k j) = -1 :=
  envelopeDetector_eq_message_of_abs_le N 1 1 1 (fun _ => -1) k _
    (fun _ => rfl) (by norm_num) (fun _ => by norm_num) (by norm_num) j

/-- At the boundary the envelope hits zero, and the nonnegative-envelope form applies. -/
example (N : ℕ) [NeZero N] (k : ZMod N) :
    (fun j => envelopeDetector 1 1 (quadratureObservation N 1 1 (fun _ => -1) k j)) =
      fun _ => -1 :=
  envelopeDetector_comp_eq_message N 1 1 (fun _ => -1) k (by norm_num) (fun _ => by norm_num)

end PhyslibExtTest.Communications.IdealAMEnvelope
