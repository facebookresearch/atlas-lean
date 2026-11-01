/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPacketQFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate

/-! Draft semantic reduction only. Every finite equality remains an explicit hypothesis.
Source masks use the executable packet formula, avoiding the octad catalogue inverse. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Complete executable source encoding, including the actual octad Omega correction. -/
def generatedTenthRootTwoCertificateSourceMask (k : Fin 4136) : ℕ :=
  generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalFifthPacketQFinite
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)).base)

/-- Exact natural source-mask obligation, with the original source row bound explicitly. -/
def GeneratedTenthRootTwoCertificateSourceCheck (k : Fin 4136) : Prop :=
  generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k =
    generatedTenthRootTwoCertificateSourceMask k

/-- Exact preferred physical target mask, retaining all three short families. -/
def GeneratedTenthRootTwoCertificateTargetCheck (k : Fin 4136) : Prop :=
  generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetMask k =
    generatedAxisGlobalShortMask
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k)

/-- All twenty-four output bits are certified against the genuine Root02 cache columns. -/
def GeneratedTenthRootTwoCertificateVectorCheck (k : Fin 4136) : Prop :=
  generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 2)
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k) =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetMask k

/-- The complete central coefficient uses the original Root02 correction rows. -/
def GeneratedTenthRootTwoCertificatePhaseCheck (k : Fin 4136) : Prop :=
  (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 2)
      (generatedAxisGlobalFifthMaskCoefficients 2)
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k)).testBit 0
    then (1 : ZMod 2) else 0) =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k

/-- Executable original numerator, using the checked coordinate-pair catalogue. -/
def generatedTenthRootTwoCertificateSourceNumerator :
    GeneratedAxisGlobalFifthShortPacketIndex → ℤ
  | Sum.inl (s, p) => generatedFifthFinalPairNumerator s
      (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2
  | Sum.inr (j, e) => generatedFifthFinalOctadNumerator j e

/-- Original signed numerator with only executable catalogue coordinates. -/
def generatedTenthRootTwoCertificateSignedNumerator (k : Fin 4136) : ℤ :=
  if generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k = 0 then
    generatedTenthRootTwoCertificateSourceNumerator
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)
  else -generatedTenthRootTwoCertificateSourceNumerator
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)

/-- The executable integer retains the exact actual Fifth source numerator. -/
theorem generatedTenth_root_two_certificate_source_numerator
    (a : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedTenthRootTwoCertificateSourceNumerator a = generatedNinthOriginalShortNumerator a := by
  rcases a with ⟨s, p⟩ | ⟨j, e⟩
  · simp only [generatedTenthRootTwoCertificateSourceNumerator,
      generatedNinthOriginalShortNumerator, generatedAxisGlobalPairCoordinates_actual]
  · rfl

/-- The full phase is preserved when binding the executable signed numerator. -/
theorem generatedTenth_root_two_certificate_signed_numerator (k : Fin 4136) :
    generatedTenthRootTwoCertificateSignedNumerator k =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator k := by
  unfold generatedTenthRootTwoCertificateSignedNumerator
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator
  rw [generatedTenth_root_two_certificate_source_numerator]

/-- Exact sparse signed coverage, including every original zero row. -/
def GeneratedTenthRootTwoCertificateCoverageCheck (k : Fin 4136) : Prop :=
  generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k) =
    generatedTenthRootTwoCertificateSignedNumerator k

/-- Every stored dictionary key binds its genuine candidate source-row target. -/
def GeneratedTenthRootTwoCertificateKeyCheck (a : Fin 3856) : Prop :=
  generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey a =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryRow a))

/-- Four explicit finite checks imply the complete source-bound full-Q row certificate. -/
theorem generatedTenth_root_two_certificate_row_of_checks (k : Fin 4136)
    (hs : GeneratedTenthRootTwoCertificateSourceCheck k)
    (ht : GeneratedTenthRootTwoCertificateTargetCheck k)
    (hv : GeneratedTenthRootTwoCertificateVectorCheck k)
    (hp : GeneratedTenthRootTwoCertificatePhaseCheck k) :
    GeneratedTenthRootTwoIncomingShortRowCertificate k := by
  refine ⟨?_, ?_, ?_⟩
  · change generatedAxisGlobalQMask
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k) = _
    rw [show generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k =
      generatedTenthRootTwoCertificateSourceMask k from hs]
    have hq := generatedAxisGlobalQMaskEncode_positive
      (generatedAxisGlobalFifthPacketQFinite
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k))
      (generatedAxisGlobalFifthPacketQFinite_positive
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k))
    exact hq.symm.trans (generatedAxisGlobalFifthPacketQFinite_eq _)
  · change generatedAxisGlobalQMask
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetMask k) = _
    rw [show generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetMask k =
      generatedAxisGlobalShortMask
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k) from ht]
    exact (generatedAxisGlobalShortMask_Q_actual _).symm.trans
      (generatedAxisGlobalShortQFinite_actual _)
  · change generatedAxisGlobalFifthQFast 2 (generatedAxisGlobalQMask _) =
      qCentral _ * generatedAxisGlobalQMask _
    rw [generatedAxisGlobalFifthQFast_mask 2 generatedAxisGlobalFifthQCache02_actual]
    exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hv hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
