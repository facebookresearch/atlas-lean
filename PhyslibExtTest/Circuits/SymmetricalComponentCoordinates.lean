/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.SymmetricalComponentCoordinates

@[expose] public section

open PhyslibExt.Circuits.SymmetricalComponentCoordinates

namespace PhyslibExtTest.Circuits.SymmetricalComponentCoordinates

/-- A balanced positive-sequence input has only its positive
sequence component, for a concrete amplitude. -/
example : zeroSequence 2 (alpha ^ 2 * 2) (alpha * 2) = 0
    ∧ positiveSequence 2 (alpha ^ 2 * 2) (alpha * 2) = 2
    ∧ negativeSequence 2 (alpha ^ 2 * 2) (alpha * 2) = 0 :=
  balanced_positive_sequence_components 2

end PhyslibExtTest.Circuits.SymmetricalComponentCoordinates
