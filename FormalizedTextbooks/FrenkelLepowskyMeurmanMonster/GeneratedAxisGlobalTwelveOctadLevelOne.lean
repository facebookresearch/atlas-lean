/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionPackedNat

/-! The first level of the octad binary forest: a descending forest on the 256 values of the
induced dual action, with roots zero, one and two. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Packed proposed ranks of the 256 dual values, in four-bit fields. -/
def generatedAxisGlobalTwelveOctadLevelRankData : ℕ :=
  generatedAxisGlobalPackedNat%[
    "49340029706702454313549837916664144192803039865775",
    "75368514614473423264841499651332640469592048346942",
    "29763782453358075863523087541903799852807848435722",
    "02675428490194844828667606163811264558775659781487",
    "11486242651329770472892282096072265121417280170635",
    "25262004079533095090468934111113678751407949407112",
    "33474560"]

/-- Packed proposed generator edges of the 256 dual values, in four-bit fields. -/
def generatedAxisGlobalTwelveOctadLevelEdgeData : ℕ :=
  generatedAxisGlobalPackedNat%[
    "42056546533514275956574201508684638505399032520318",
    "47772472920294773747853480727587280943217883068026",
    "46624705328797833409906321703737786083523662356939",
    "97009784483173244973834421083961195427445792862040",
    "91570065284881175101562954040222552178505101904943",
    "33122617473256823757099703051035724823550483325024",
    "74752"]

/-- The proposed rank of a dual value. -/
def generatedAxisGlobalTwelveOctadLevelRank (y : ℕ) : ℕ :=
  (generatedAxisGlobalTwelveOctadLevelRankData >>> (4 * y)) % 16

/-- The proposed generator edge of a dual value. -/
def generatedAxisGlobalTwelveOctadLevelEdge (y : ℕ) : Fin 16 :=
  ⟨(generatedAxisGlobalTwelveOctadLevelEdgeData >>> (4 * y)) % 16, Nat.mod_lt _ (by decide)⟩

/-- One dual value is a root or has a strictly descending generator image. -/
def generatedAxisGlobalTwelveOctadLevelStep (y : ℕ) : Prop :=
  y = 0 ∨ y = 1 ∨ y = 2 ∨
    generatedAxisGlobalTwelveOctadLevelRank
        (generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalTwelveOctadCoordRows (generatedAxisGlobalTwelveOctadLevelEdge y))
          (y <<< 16) >>> 16) <
      generatedAxisGlobalTwelveOctadLevelRank y

set_option maxHeartbeats 40000000 in
-- Check all 256 dual values.
/-- Every dual value is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadLevel_certificate : ∀ y : Fin 256,
    generatedAxisGlobalTwelveOctadLevelStep y.val := by
  unfold generatedAxisGlobalTwelveOctadLevelStep
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
