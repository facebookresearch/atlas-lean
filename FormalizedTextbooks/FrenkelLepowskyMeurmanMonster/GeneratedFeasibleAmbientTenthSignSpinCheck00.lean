/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthFastMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignDataB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthBlocks

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 0 are checked.
private theorem sg_0_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 0 are checked.
private theorem sg_0_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 0 are checked.
private theorem sg_0_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 0 are checked.
private theorem sg_0_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 0 are checked.
private theorem sg_0_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 0 are checked.
private theorem sg_0_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 0 are checked.
private theorem sg_0_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 0 are checked.
private theorem sg_0_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 0 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 0 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 1 are checked.
private theorem sg_1_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 1 are checked.
private theorem sg_1_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 1 are checked.
private theorem sg_1_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 1 are checked.
private theorem sg_1_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 1 are checked.
private theorem sg_1_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 1 are checked.
private theorem sg_1_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 1 are checked.
private theorem sg_1_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 1 are checked.
private theorem sg_1_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 1 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 1 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 2 are checked.
private theorem sg_2_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 2 are checked.
private theorem sg_2_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 2 are checked.
private theorem sg_2_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 2 are checked.
private theorem sg_2_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 2 are checked.
private theorem sg_2_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 2 are checked.
private theorem sg_2_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 2 are checked.
private theorem sg_2_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 2 are checked.
private theorem sg_2_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 2 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 2 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 3 are checked.
private theorem sg_3_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 3 are checked.
private theorem sg_3_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 3 are checked.
private theorem sg_3_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 3 are checked.
private theorem sg_3_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 3 are checked.
private theorem sg_3_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 3 are checked.
private theorem sg_3_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 3 are checked.
private theorem sg_3_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 3 are checked.
private theorem sg_3_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 3 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 3 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 4 are checked.
private theorem sg_4_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 4 are checked.
private theorem sg_4_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 4 are checked.
private theorem sg_4_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 4 are checked.
private theorem sg_4_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 4 are checked.
private theorem sg_4_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 4 are checked.
private theorem sg_4_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 4 are checked.
private theorem sg_4_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 4 are checked.
private theorem sg_4_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 4 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 4 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 5 are checked.
private theorem sg_5_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 5 are checked.
private theorem sg_5_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 5 are checked.
private theorem sg_5_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 5 are checked.
private theorem sg_5_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 5 are checked.
private theorem sg_5_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 5 are checked.
private theorem sg_5_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 5 are checked.
private theorem sg_5_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 5 are checked.
private theorem sg_5_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 5 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 5 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 6 are checked.
private theorem sg_6_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 6 are checked.
private theorem sg_6_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 6 are checked.
private theorem sg_6_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 6 are checked.
private theorem sg_6_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 6 are checked.
private theorem sg_6_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 6 are checked.
private theorem sg_6_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 6 are checked.
private theorem sg_6_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 6 are checked.
private theorem sg_6_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 6 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 6 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 of factor 7 are checked.
private theorem sg_7_0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 0 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 0 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 of factor 7 are checked.
private theorem sg_7_1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 1 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 1 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 of factor 7 are checked.
private theorem sg_7_2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 2 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 2 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 of factor 7 are checked.
private theorem sg_7_3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 3 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 3 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 of factor 7 are checked.
private theorem sg_7_4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 4 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 4 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 of factor 7 are checked.
private theorem sg_7_5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 5 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 5 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 of factor 7 are checked.
private theorem sg_7_6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 6 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 6 a)
          := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 of factor 7 are checked.
private theorem sg_7_7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 7 (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) (generatedFeasibleAmbientTenthBlockLabel 7 a) =
      2 * generatedFeasibleAmbientTenthSignSpin 0 7 (generatedFeasibleAmbientTenthBlockLabel 7 a)
          := by
  decide +kernel

/-- The source sign of root-two stage 0 after its cached monomial pullback. -/
theorem generatedFeasibleAmbientTenth_sign_spin_check00 : ∀ (r : Fin 8) (a : Fin 4096),
    generatedFeasibleAmbientTenthSignSpinCompactF 0
        (fun b => generatedFeasibleAmbientTenthMonomialPhaseSignF 0 b *
            generatedFeasibleAmbientTenthSpin 0 r (generatedFeasibleAmbientTenthMonomialPullF 0
            b)) a =
      2 * generatedFeasibleAmbientTenthSignSpin 0 r a := by
  intro r
  fin_cases r
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_0_0
    · exact sg_0_1
    · exact sg_0_2
    · exact sg_0_3
    · exact sg_0_4
    · exact sg_0_5
    · exact sg_0_6
    · exact sg_0_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_1_0
    · exact sg_1_1
    · exact sg_1_2
    · exact sg_1_3
    · exact sg_1_4
    · exact sg_1_5
    · exact sg_1_6
    · exact sg_1_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_2_0
    · exact sg_2_1
    · exact sg_2_2
    · exact sg_2_3
    · exact sg_2_4
    · exact sg_2_5
    · exact sg_2_6
    · exact sg_2_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_3_0
    · exact sg_3_1
    · exact sg_3_2
    · exact sg_3_3
    · exact sg_3_4
    · exact sg_3_5
    · exact sg_3_6
    · exact sg_3_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_4_0
    · exact sg_4_1
    · exact sg_4_2
    · exact sg_4_3
    · exact sg_4_4
    · exact sg_4_5
    · exact sg_4_6
    · exact sg_4_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_5_0
    · exact sg_5_1
    · exact sg_5_2
    · exact sg_5_3
    · exact sg_5_4
    · exact sg_5_5
    · exact sg_5_6
    · exact sg_5_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_6_0
    · exact sg_6_1
    · exact sg_6_2
    · exact sg_6_3
    · exact sg_6_4
    · exact sg_6_5
    · exact sg_6_6
    · exact sg_6_7
  · apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact sg_7_0
    · exact sg_7_1
    · exact sg_7_2
    · exact sg_7_3
    · exact sg_7_4
    · exact sg_7_5
    · exact sg_7_6
    · exact sg_7_7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
