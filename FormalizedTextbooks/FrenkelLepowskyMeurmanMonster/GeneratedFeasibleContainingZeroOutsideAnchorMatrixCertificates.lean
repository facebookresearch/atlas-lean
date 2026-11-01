/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixPacket07

/-! Every entry of all three complete physical matrix equations is retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem matrix_address (i : Fin 24) :
    ∃ k : Fin 8, ∃ q : Fin 3, generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex k q = i := by
  let k : Fin 8 := ⟨i.val / 3, by omega⟩
  let q : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
  exact ⟨k, q, Fin.ext (by dsimp [generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex, k, q]; omega)⟩

/-- All576 physical coordinates follow from the complete bounded original certificates. -/
theorem generatedFeasibleContainingZeroOutsideAnchorMatrix_source : co1XiMatrixQ * generatedFeasibleContainingZeroOutsideAnchorSourceProjectionQ * co1XiMatrixQ.transpose = generatedFeasibleContainingZeroOutsideAnchorMatrix1Q := by
  ext i j
  obtain ⟨k, q, hq⟩ := matrix_address i
  rw [← hq]
  fin_cases k
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket00_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket01_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket02_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket03_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket04_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket05_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket06_source q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket07_source q j

/-- All576 physical coordinates follow from the complete bounded original certificates. -/
theorem generatedFeasibleContainingZeroOutsideAnchorMatrix_triality : generatedFeasibleContainingZeroOutsideAnchorForwardMatrixQ = generatedFeasibleContainingZeroOutsideAnchorMatrix2Q := by
  ext i j
  obtain ⟨k, q, hq⟩ := matrix_address i
  rw [← hq]
  fin_cases k
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket00_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket01_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket02_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket03_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket04_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket05_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket06_triality q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket07_triality q j

/-- All576 physical coordinates follow from the complete bounded original certificates. -/
theorem generatedFeasibleContainingZeroOutsideAnchorMatrix_target : co1XiMatrixQ * generatedFeasibleContainingZeroOutsideAnchorMatrix2Q * co1XiMatrixQ.transpose = generatedFeasibleContainingZeroOutsideAnchorTargetProjectionQ := by
  ext i j
  obtain ⟨k, q, hq⟩ := matrix_address i
  rw [← hq]
  fin_cases k
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket00_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket01_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket02_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket03_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket04_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket05_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket06_target q j
  · exact generatedFeasibleContainingZeroOutsideAnchorMatrixPacket07_target q j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
