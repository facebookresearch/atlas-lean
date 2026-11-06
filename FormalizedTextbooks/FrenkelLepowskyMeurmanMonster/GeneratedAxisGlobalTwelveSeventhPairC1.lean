/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhPairs

/-! # Seventh cell 22 from the identification of record gforest:S7c1-

The target word of `s7c1n_ident` is an Xi-free prefix followed by the cell word of Seventh cell
`22`; the Q-phase lemma `seventhCell_of_seventh_neg` (with the phase of the prefix computed in
the kernel) binds the inverse triality image of the Seventh cell 22 vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word of record gforest:S7c1-. -/
def s7c1nPrefix : List IdentLetter :=
  [.qel (qmElt (9781912, false)), .sign 128 0, .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false)]

/-- The target word is the prefix followed by the cell word of Seventh cell 22. -/
theorem s7c1nG_split : s7c1nG = s7c1nPrefix ++ seventhCellIdent 22 := rfl

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix flips the central sign. -/
theorem s7c1nPrefix_phase :
    qmWord (s7c1nPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The inverse triality image of the Seventh cell 22 vector lies in the twelve local orbits. -/
theorem seventhCell22_neg_of_C1n :
    sExtra⁻¹ (rhoLocal (seventhCellWord 22) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h := seventhCell_of_seventh_neg 1 22 s7c1nPrefix (by simp [s7c1nPrefix, SixthPhaseLetter])
    (by simp [s7c1nPrefix]) (by rw [← s7c1nG_split]; exact s7c1n_cell)
  exact h.2 s7c1nPrefix_phase

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
