/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparseRationalShortOutputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingFast

/-! Every original actual outgoing Fourth short coordinate retains its complete Fourier inputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The entire genuine original outgoing short operator with true incoming zero guards. -/
def generatedAxisGlobalOddFourthSparseOutgoingShort (k : Fin 4) : GriessShortIndex → ℚ :=
  let A := if k.val < 2 then generatedAxisGlobalOddRoot02RationalPacket
    else generatedAxisGlobalOddRoot04RationalPacket
  if k = 0 ∨ k = 2 then generatedAxisGlobalSparseTrialityShortQ A
    else generatedAxisGlobalSparseInverseShortQ A

/-- Every source coefficient equals the whole actual original outgoing short packet. -/
theorem generatedAxisGlobalOddFourthSparseOutgoingShort_eq (k : Fin 4) (r : GriessShortIndex) :
    generatedAxisGlobalOddFourthSparseOutgoingShort k r = (generatedAxisGlobalOddFourthOutgoingPacket k).2.1 r := by
  fin_cases k <;>
    simp [generatedAxisGlobalOddFourthSparseOutgoingShort, generatedAxisGlobalOddFourthOutgoingPacket,
      generatedAxisGlobalRationalTriality, generatedAxisGlobalRationalInverse,
      generatedAxisGlobalSparseTrialityShortQ_eq, generatedAxisGlobalSparseInverseShortQ_eq]

/-- The complete original selected phase and source coefficient, with the true Fourier zero guard. -/
def generatedAxisGlobalOddFourthSparseSelectedShortQ (k : Fin 4) (j : Fin 4584) : ℚ :=
  (generatedAxisGlobalIntSign (generatedAxisGlobalOddFourthSelectedPhase k j) : ℚ) *
    generatedAxisGlobalOddFourthSparseOutgoingShort k (generatedAxisGlobalOddFourthSelectedSource k j)

/-- Every selected coefficient is exactly the original full signed coefficient. -/
theorem generatedAxisGlobalOddFourthSparseSelectedShortQ_eq (k : Fin 4) (j : Fin 4584) :
    generatedAxisGlobalOddFourthSparseSelectedShortQ k j = generatedAxisGlobalOddFourthSelectedShortQ k j := by
  unfold generatedAxisGlobalOddFourthSparseSelectedShortQ generatedAxisGlobalOddFourthSelectedShortQ
  rw [generatedAxisGlobalOddFourthSparseOutgoingShort_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
