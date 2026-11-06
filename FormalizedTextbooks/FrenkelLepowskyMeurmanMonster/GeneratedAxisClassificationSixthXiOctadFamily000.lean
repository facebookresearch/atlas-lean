/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressFixed

/-! Discovered sparse targets are checked against the genuine original binary and phase actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Candidate sparse outputs for all 64 preferred signs of the first actual source octad family. -/
def generatedSixthXiOctadFamily000Output : Fin 64 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (0, 10)),
    Sum.inr (Sum.inl (0, 6)),
    Sum.inl 234,
    Sum.inl 172,
    Sum.inr (Sum.inl (0, 3)),
    Sum.inr (Sum.inl (0, 2)),
    Sum.inl 210,
    Sum.inl 212,
    Sum.inr (Sum.inl (0, 15)),
    Sum.inr (Sum.inl (0, 14)),
    Sum.inl 213,
    Sum.inl 211,
    Sum.inr (Sum.inl (0, 11)),
    Sum.inr (Sum.inl (0, 7)),
    Sum.inl 173,
    Sum.inl 235,
    Sum.inl 499,
    Sum.inl 195,
    Sum.inr (Sum.inl (0, 21)),
    Sum.inr (Sum.inl (0, 25)),
    Sum.inl 265,
    Sum.inl 297,
    Sum.inr (Sum.inl (0, 28)),
    Sum.inr (Sum.inl (0, 29)),
    Sum.inl 296,
    Sum.inl 264,
    Sum.inr (Sum.inl (0, 16)),
    Sum.inr (Sum.inl (0, 17)),
    Sum.inl 194,
    Sum.inl 498,
    Sum.inr (Sum.inl (0, 20)),
    Sum.inr (Sum.inl (0, 24)),
    Sum.inl 511,
    Sum.inl 197,
    Sum.inr (Sum.inl (0, 37)),
    Sum.inr (Sum.inl (0, 41)),
    Sum.inl 267,
    Sum.inl 299,
    Sum.inr (Sum.inl (0, 44)),
    Sum.inr (Sum.inl (0, 45)),
    Sum.inl 298,
    Sum.inl 266,
    Sum.inr (Sum.inl (0, 32)),
    Sum.inr (Sum.inl (0, 33)),
    Sum.inl 196,
    Sum.inl 510,
    Sum.inr (Sum.inl (0, 36)),
    Sum.inr (Sum.inl (0, 40)),
    Sum.inr (Sum.inl (0, 55)),
    Sum.inr (Sum.inl (0, 59)),
    Sum.inl 522,
    Sum.inl 200,
    Sum.inr (Sum.inl (0, 62)),
    Sum.inr (Sum.inl (0, 63)),
    Sum.inl 270,
    Sum.inl 302,
    Sum.inr (Sum.inl (0, 50)),
    Sum.inr (Sum.inl (0, 51)),
    Sum.inl 303,
    Sum.inl 271,
    Sum.inr (Sum.inl (0, 54)),
    Sum.inr (Sum.inl (0, 58)),
    Sum.inl 201,
    Sum.inl 523]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 24000000 in
-- Check all original binary bits, complete central phases and signed coefficient numerators.
/-- Every candidate output has its genuine original binary image and complete signed coefficient. -/
theorem generatedSixth_xi_octad_family000_certificate (e : Fin 64) :
    let x : GeneratedSixthXiShortAddress := Sum.inr (Sum.inl (0, e))
    let y := generatedSixthXiOctadFamily000Output e
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMask x) =
      generatedSixthXiShortAddressMask y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMask x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  revert e
  decide +kernel

/-- All checked outputs are fixed by the original corrected Xi action, with no lost signs. -/
theorem generatedSixth_xi_octad_family000_fixed (e : Fin 64) :
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1
        (generatedSixthXiShortAddressIndex (generatedSixthXiOctadFamily000Output e)) =
      (griessConwayEncode generatedSixthAxis).2.1
        (generatedSixthXiShortAddressIndex (generatedSixthXiOctadFamily000Output e)) :=
  generatedSixth_xi_short_address_fixed _ _
    (generatedSixth_xi_octad_family000_certificate e).1
    (generatedSixth_xi_octad_family000_certificate e).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
