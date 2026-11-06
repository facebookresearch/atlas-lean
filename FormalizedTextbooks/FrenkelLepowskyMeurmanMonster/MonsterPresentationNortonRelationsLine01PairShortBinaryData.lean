/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact binary coordinates of the first reached octad packet and its inverse-U images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortInput

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Finite masks for the actual input shortest-vector Q coordinates. -/
def monsterNortonLine01PairInputBinaryMasks : Fin 64 → ℕ :=
  ![
    0x401501, 0x7ad01, 0x6f5d01, 0x28ed01, 0x635d01, 0x24ed01, 0x4c1d01, 0xba501,
    0x6b5d01, 0x2ced01, 0x441d01, 0x3a501, 0x481d01, 0xfa501, 0x675501, 0x20e501,
    0x274d01, 0x60fd01, 0x80d01, 0x4fb501, 0x40d01, 0x43b501, 0x2b4501, 0x6cf501,
    0xc0d01, 0x4bb501, 0x234501, 0x64f501, 0x2f4501, 0x68f501, 0x501, 0x47bd01,
    0x4d7d01, 0xacd01, 0x623d01, 0x258501, 0x6e3d01, 0x298501, 0x417501, 0x6c501,
    0x663d01, 0x218501, 0x497501, 0xec501, 0x457501, 0x2c501, 0x6a3501, 0x2d8d01,
    0x2a2d01, 0x6d9501, 0x56501, 0x42d501, 0x96501, 0x4ed501, 0x262501, 0x619d01,
    0x16501, 0x46d501, 0x2e2501, 0x699d01, 0x222501, 0x659d01, 0xd6d01, 0x4add01]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every binary coordinate against the original integral-short dictionary.
/-- All input masks agree with actual Q coordinates, by direct kernel certificates. -/
theorem monsterNortonLine01PairInputBinaryMasks_actual (e : Fin 64) :
    toAdd (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e)).base =
      (fun i : Fin 24 =>
        if (monsterNortonLine01PairInputBinaryMasks e).testBit i.val then 1 else 0) := by
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairInverseInputIntegral_actual]
  funext i
  revert i
  fin_cases e <;> decide +kernel

/-- Finite masks for the actual output shortest-vector Q coordinates. -/
def monsterNortonLine01PairOutputBinaryMasks : Fin 64 → ℕ :=
  ![
    0x2a0800, 0x2a0803, 0x60c951, 0x20c95e, 0x42c150, 0x2c15f, 0x48000d, 0x48000e,
    0x48c15e, 0x8c151, 0x420003, 0x420000, 0x600802, 0x600801, 0x2ac953, 0x6ac95c,
    0x2ac15f, 0x6ac150, 0x200002, 0x200001, 0x20803, 0x20800, 0x48c952, 0x8c95d,
    0x8080d, 0x8080e, 0x42c95c, 0x2c953, 0x60c15d, 0x20c152, 0x6a0000, 0x6a0003,
    0x6a000d, 0x2a0002, 0x60c150, 0x60c153, 0x42c951, 0x42c952, 0x80800, 0x48080f,
    0x48c95f, 0x48c95c, 0x2080e, 0x420801, 0x20000f, 0x600000, 0x2ac152, 0x2ac151,
    0x2ac95e, 0x2ac95d, 0x60080f, 0x200800, 0x42000e, 0x20001, 0x48c153, 0x48c150,
    0x480000, 0x8000f, 0x42c15d, 0x42c15e, 0x60c95c, 0x60c95f, 0x2a080d, 0x6a0802]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every binary coordinate against the original integral-short dictionary.
/-- All output masks agree with actual Q coordinates, by direct kernel certificates. -/
theorem monsterNortonLine01PairOutputBinaryMasks_actual (e : Fin 64) :
    toAdd (monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e)).base =
      (fun i : Fin 24 =>
        if (monsterNortonLine01PairOutputBinaryMasks e).testBit i.val then 1 else 0) := by
  unfold monsterNortonShortQ
  rw [monsterNortonLine01PairInverseShortIntegral_actual]
  funext i
  revert i
  fin_cases e <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
