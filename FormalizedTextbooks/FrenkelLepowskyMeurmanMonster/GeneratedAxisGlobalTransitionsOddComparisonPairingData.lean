/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonRationalData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseSources
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSparsePairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse

/-! Exact full scalar pairings for three literal original local comparison words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
open scoped BigOperators

/-- The complete original rational input uses its exact sparse short constituent. -/
def generatedAxisGlobalOddSparseRootPacket (k : Fin 2) : GeneratedAxisGlobalRationalPacket :=
  ((generatedAxisGlobalOddRationalRootPacket k).1,
    (generatedAxisGlobalOddSparseShortQ ⟨k.val, by omega⟩,
      (generatedAxisGlobalOddRationalRootPacket k).2.2))

/-- Three complete original outgoing rational packets, with true forward or inverse source action. -/
def generatedAxisGlobalOddComparisonTransitionPacket (k : Fin 3) :
    GeneratedAxisGlobalRationalPacket :=
  if k = 0 then generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 0)
  else if k = 1 then
    generatedAxisGlobalRationalInverse (generatedAxisGlobalOddSparseRootPacket 0)
  else generatedAxisGlobalRationalInverse (generatedAxisGlobalOddSparseRootPacket 1)

/-- Every physical matrix entry contributes its exact original rational pairing. -/
def generatedAxisGlobalOddComparisonMatrixPairingQ (k : Fin 3) : ℚ :=
  ∑ i : Fin 24, ∑ j : Fin 24,
    (generatedAxisGlobalOddComparisonTransitionPacket k).1 i j *
      generatedAxisGlobalOddComparisonMatrixQ k i j

/-- All 552 genuine target source coordinates contribute their exact outgoing short coefficient. -/
def generatedAxisGlobalOddComparisonShortPairingQ (k : Fin 3) : ℚ :=
  ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
    generatedAxisGlobalOddSparseCoefficient ⟨k.val + 2, by omega⟩ p *
      (generatedAxisGlobalOddComparisonTransitionPacket k).2.1
        (generatedAxisGlobalOddSparseLabel ⟨k.val + 2, by omega⟩ p)

/-- The entire tensor pairing uses its true original source denominator and complete target factors. -/
def generatedAxisGlobalOddComparisonTensorPairingQ (k : Fin 3) : ℚ :=
  generatedAxisGlobalRationalTensorSparsePairing
    (generatedAxisGlobalOddComparisonTransitionPacket k).2.2
    (generatedAxisGlobalOddRationalComparisonSpin k)
    (generatedAxisGlobalOddRationalComparisonSpatial k)
    (generatedAxisGlobalOddRationalComparisonDenominator k)

/-- The sum is the full physical matrix, signed-short and tensor pairing. -/
def generatedAxisGlobalOddComparisonPairingQ (k : Fin 3) : ℚ :=
  generatedAxisGlobalOddComparisonMatrixPairingQ k +
    generatedAxisGlobalOddComparisonShortPairingQ k +
      generatedAxisGlobalOddComparisonTensorPairingQ k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
