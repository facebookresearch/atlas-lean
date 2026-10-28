/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBalancedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCacheNatural

/-! Future packet rewrite helpers. Original finite predicates remain unchanged.
All new symbolic proof bodies are uncompiled drafts. No source octad inverse is evaluated. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The exact original source theta vector uses the complete frozen Parker mask cache. -/
def generatedTenthRootTwoRewriteSourceTheta (d : Fin 4096) (k : Fin 12) : ZMod 2 :=
  if (generatedTwelfthParkerThetaCacheNatural d.val).testBit k.val then 1 else 0

/-- The complete cached theta vector equals the original source vector at every coordinate. -/
theorem generatedTenth_root_two_rewrite_source_theta (d : Fin 4096) :
    generatedTenthRootTwoRewriteSourceTheta d = sourceWordTheta d := by
  funext k
  unfold generatedTenthRootTwoRewriteSourceTheta sourceWordTheta
  rw [generatedTwelfth_parker_theta_cache_natural_actual]

/-- Exact full packet Q source, with the original code, Omega, syndrome and central coefficient. -/
def generatedTenthRootTwoRewritePacketQ : GeneratedAxisGlobalFifthShortPacketIndex → Q
  | Sum.inl (s, p) => generatedAxisGlobalPairQFinite s p
  | Sum.inr (j, e) =>
      ⟨ofAdd (Fin.append
        (golayLabelCoefficients (generatedFifthEvenRootCode j) +
          griessOctadOmegaCoefficient e • Pi.single 11 1)
        (generatedTenthRootTwoRewriteSourceTheta (generatedFifthEvenRootCode j) +
          golaySyndrome (integerParity (generatedAxisGlobalFifthShortNegativeInteger j e)))), 1⟩

/-- Cached source evaluation equals the entire original finite Q element, including phase. -/
theorem generatedTenth_root_two_rewrite_packet_Q_actual
    (a : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedTenthRootTwoRewritePacketQ a = generatedAxisGlobalFifthPacketQFinite a := by
  rcases a with ⟨s, p⟩ | ⟨j, e⟩
  · rfl
  · simp only [generatedTenthRootTwoRewritePacketQ, generatedAxisGlobalFifthPacketQFinite,
      generatedAxisGlobalFifthShortPacketQ, generatedTenth_root_two_rewrite_source_theta]

/-- Encoding the cached full source uses the same original twenty-four binary coordinates. -/
def generatedTenthRootTwoRewriteSourceMask (k : Fin 4136) : ℕ :=
  generatedAxisGlobalMaskEncode (toAdd (generatedTenthRootTwoRewritePacketQ
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)).base)

/-- This rewrite preserves the literal source row and its exact original encoded natural mask. -/
theorem generatedTenth_root_two_rewrite_source_mask_actual (k : Fin 4136) :
    generatedTenthRootTwoCertificateSourceMask k = generatedTenthRootTwoRewriteSourceMask k := by
  unfold generatedTenthRootTwoCertificateSourceMask generatedTenthRootTwoRewriteSourceMask
  rw [generatedTenth_root_two_rewrite_packet_Q_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
