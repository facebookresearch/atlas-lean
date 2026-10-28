/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An exact primitive certificate in the integer fixed-vector test of Norton u. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- Release each finite block reduction before checking the next block.
set_option Elab.async false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_0 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 0 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 0 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_1 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 1 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 1 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_2 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 2 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 2 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_3 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 3 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 3 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_4 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 4 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 4 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_5 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 5 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 5 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_6 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 6 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 6 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_7 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 7 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 7 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_8 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 8 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 8 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_9 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 9 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 9 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_10 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 10 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 10 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_11 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 11 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 11 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_12 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 12 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 12 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_13 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 13 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 13 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_14 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 14 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 14 n) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify one 256-coordinate block against the exact actual primitive numerator.
private theorem chunk_15 : ∀ n : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex 15 n) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex 15 n) := by
  decide +kernel

/-- The complete exact integer equality for primitive number 3 of the fixed-vector test. -/
theorem monsterNortonFixedPrimitive3 :
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) =
      monsterNortonFixedState 4 := by
  funext n
  have h : ∀ k : Fin 16, ∀ m : Fin 256,
    monsterNortonSpinPrimitive 3 (monsterNortonFixedState 3) (monsterNortonFixedChunkIndex k m) =
      monsterNortonFixedState 4 (monsterNortonFixedChunkIndex k m) := by
    intro k
    fin_cases k
    · exact chunk_0
    · exact chunk_1
    · exact chunk_2
    · exact chunk_3
    · exact chunk_4
    · exact chunk_5
    · exact chunk_6
    · exact chunk_7
    · exact chunk_8
    · exact chunk_9
    · exact chunk_10
    · exact chunk_11
    · exact chunk_12
    · exact chunk_13
    · exact chunk_14
    · exact chunk_15
  have hn := h (monsterNortonFixedChunkBlock n) (monsterNortonFixedChunkOffset n)
  simpa only [monsterNortonFixedChunkIndex_block_offset] using hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
