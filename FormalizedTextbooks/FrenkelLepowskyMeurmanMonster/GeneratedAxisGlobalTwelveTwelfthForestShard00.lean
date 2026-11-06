/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestStep
public import Mathlib.Tactic.FinCases

/-! Checked Twelfth forest descent for the blocks `256 * 0` to `256 * 0 + 255`, that is, for the
coordinate masks below `2 ^ 24` whose high twelve bits lie in that range. Every check is a kernel
evaluation of the sound Boolean obligations of one 4096-mask block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 0 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0000 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 0)
      (4096 * 0) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 1 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0001 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 1)
      (4096 * 1) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 2 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0002 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 2)
      (4096 * 2) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 3 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0003 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 3)
      (4096 * 3) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 4 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0004 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 4)
      (4096 * 4) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 5 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0005 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 5)
      (4096 * 5) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 6 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0006 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 6)
      (4096 * 6) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 7 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0007 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 7)
      (4096 * 7) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 8 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0008 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 8)
      (4096 * 8) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 9 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0009 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 9)
      (4096 * 9) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 10 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0010 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 10)
      (4096 * 10) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 11 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0011 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 11)
      (4096 * 11) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 12 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0012 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 12)
      (4096 * 12) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 13 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0013 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 13)
      (4096 * 13) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 14 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0014 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 14)
      (4096 * 14) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 15 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0015 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 15)
      (4096 * 15) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 0 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup000 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 0 + t.val)) (4096 * (16 * 0 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0000
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0001
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0002
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0003
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0004
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0005
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0006
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0007
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0008
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0009
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0010
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0011
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0012
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0013
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0014
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0015

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 16 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0016 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 16)
      (4096 * 16) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 17 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0017 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 17)
      (4096 * 17) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 18 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0018 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 18)
      (4096 * 18) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 19 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0019 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 19)
      (4096 * 19) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 20 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0020 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 20)
      (4096 * 20) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 21 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0021 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 21)
      (4096 * 21) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 22 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0022 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 22)
      (4096 * 22) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 23 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0023 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 23)
      (4096 * 23) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 24 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0024 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 24)
      (4096 * 24) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 25 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0025 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 25)
      (4096 * 25) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 26 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0026 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 26)
      (4096 * 26) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 27 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0027 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 27)
      (4096 * 27) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 28 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0028 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 28)
      (4096 * 28) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 29 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0029 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 29)
      (4096 * 29) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 30 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0030 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 30)
      (4096 * 30) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 31 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0031 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 31)
      (4096 * 31) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 1 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup001 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 1 + t.val)) (4096 * (16 * 1 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0016
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0017
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0018
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0019
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0020
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0021
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0022
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0023
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0024
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0025
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0026
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0027
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0028
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0029
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0030
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0031

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 32 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0032 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 32)
      (4096 * 32) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 33 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0033 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 33)
      (4096 * 33) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 34 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0034 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 34)
      (4096 * 34) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 35 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0035 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 35)
      (4096 * 35) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 36 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0036 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 36)
      (4096 * 36) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 37 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0037 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 37)
      (4096 * 37) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 38 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0038 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 38)
      (4096 * 38) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 39 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0039 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 39)
      (4096 * 39) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 40 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0040 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 40)
      (4096 * 40) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 41 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0041 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 41)
      (4096 * 41) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 42 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0042 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 42)
      (4096 * 42) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 43 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0043 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 43)
      (4096 * 43) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 44 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0044 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 44)
      (4096 * 44) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 45 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0045 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 45)
      (4096 * 45) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 46 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0046 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 46)
      (4096 * 46) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 47 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0047 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 47)
      (4096 * 47) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 2 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup002 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 2 + t.val)) (4096 * (16 * 2 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0032
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0033
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0034
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0035
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0036
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0037
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0038
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0039
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0040
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0041
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0042
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0043
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0044
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0045
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0046
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0047

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 48 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0048 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 48)
      (4096 * 48) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 49 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0049 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 49)
      (4096 * 49) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 50 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0050 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 50)
      (4096 * 50) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 51 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0051 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 51)
      (4096 * 51) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 52 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0052 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 52)
      (4096 * 52) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 53 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0053 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 53)
      (4096 * 53) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 54 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0054 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 54)
      (4096 * 54) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 55 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0055 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 55)
      (4096 * 55) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 56 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0056 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 56)
      (4096 * 56) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 57 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0057 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 57)
      (4096 * 57) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 58 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0058 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 58)
      (4096 * 58) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 59 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0059 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 59)
      (4096 * 59) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 60 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0060 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 60)
      (4096 * 60) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 61 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0061 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 61)
      (4096 * 61) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 62 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0062 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 62)
      (4096 * 62) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 63 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0063 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 63)
      (4096 * 63) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 3 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup003 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 3 + t.val)) (4096 * (16 * 3 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0048
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0049
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0050
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0051
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0052
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0053
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0054
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0055
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0056
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0057
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0058
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0059
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0060
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0061
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0062
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0063

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 64 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0064 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 64)
      (4096 * 64) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 65 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0065 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 65)
      (4096 * 65) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 66 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0066 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 66)
      (4096 * 66) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 67 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0067 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 67)
      (4096 * 67) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 68 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0068 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 68)
      (4096 * 68) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 69 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0069 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 69)
      (4096 * 69) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 70 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0070 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 70)
      (4096 * 70) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 71 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0071 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 71)
      (4096 * 71) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 72 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0072 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 72)
      (4096 * 72) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 73 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0073 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 73)
      (4096 * 73) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 74 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0074 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 74)
      (4096 * 74) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 75 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0075 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 75)
      (4096 * 75) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 76 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0076 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 76)
      (4096 * 76) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 77 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0077 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 77)
      (4096 * 77) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 78 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0078 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 78)
      (4096 * 78) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 79 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0079 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 79)
      (4096 * 79) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 4 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup004 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 4 + t.val)) (4096 * (16 * 4 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0064
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0065
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0066
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0067
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0068
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0069
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0070
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0071
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0072
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0073
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0074
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0075
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0076
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0077
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0078
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0079

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 80 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0080 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 80)
      (4096 * 80) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 81 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0081 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 81)
      (4096 * 81) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 82 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0082 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 82)
      (4096 * 82) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 83 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0083 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 83)
      (4096 * 83) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 84 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0084 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 84)
      (4096 * 84) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 85 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0085 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 85)
      (4096 * 85) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 86 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0086 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 86)
      (4096 * 86) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 87 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0087 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 87)
      (4096 * 87) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 88 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0088 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 88)
      (4096 * 88) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 89 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0089 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 89)
      (4096 * 89) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 90 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0090 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 90)
      (4096 * 90) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 91 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0091 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 91)
      (4096 * 91) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 92 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0092 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 92)
      (4096 * 92) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 93 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0093 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 93)
      (4096 * 93) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 94 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0094 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 94)
      (4096 * 94) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 95 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0095 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 95)
      (4096 * 95) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 5 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup005 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 5 + t.val)) (4096 * (16 * 5 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0080
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0081
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0082
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0083
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0084
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0085
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0086
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0087
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0088
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0089
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0090
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0091
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0092
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0093
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0094
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0095

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 96 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0096 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 96)
      (4096 * 96) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 97 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0097 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 97)
      (4096 * 97) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 98 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0098 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 98)
      (4096 * 98) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 99 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0099 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 99)
      (4096 * 99) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 100 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0100 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 100)
      (4096 * 100) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 101 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0101 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 101)
      (4096 * 101) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 102 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0102 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 102)
      (4096 * 102) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 103 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0103 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 103)
      (4096 * 103) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 104 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0104 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 104)
      (4096 * 104) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 105 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0105 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 105)
      (4096 * 105) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 106 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0106 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 106)
      (4096 * 106) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 107 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0107 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 107)
      (4096 * 107) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 108 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0108 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 108)
      (4096 * 108) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 109 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0109 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 109)
      (4096 * 109) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 110 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0110 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 110)
      (4096 * 110) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 111 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0111 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 111)
      (4096 * 111) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 6 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup006 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 6 + t.val)) (4096 * (16 * 6 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0096
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0097
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0098
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0099
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0100
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0101
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0102
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0103
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0104
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0105
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0106
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0107
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0108
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0109
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0110
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0111

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 112 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0112 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 112)
      (4096 * 112) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 113 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0113 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 113)
      (4096 * 113) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 114 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0114 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 114)
      (4096 * 114) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 115 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0115 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 115)
      (4096 * 115) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 116 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0116 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 116)
      (4096 * 116) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 117 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0117 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 117)
      (4096 * 117) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 118 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0118 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 118)
      (4096 * 118) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 119 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0119 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 119)
      (4096 * 119) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 120 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0120 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 120)
      (4096 * 120) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 121 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0121 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 121)
      (4096 * 121) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 122 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0122 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 122)
      (4096 * 122) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 123 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0123 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 123)
      (4096 * 123) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 124 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0124 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 124)
      (4096 * 124) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 125 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0125 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 125)
      (4096 * 125) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 126 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0126 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 126)
      (4096 * 126) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 127 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0127 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 127)
      (4096 * 127) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 7 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup007 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 7 + t.val)) (4096 * (16 * 7 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0112
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0113
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0114
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0115
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0116
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0117
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0118
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0119
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0120
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0121
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0122
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0123
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0124
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0125
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0126
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0127

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 128 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0128 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 128)
      (4096 * 128) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 129 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0129 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 129)
      (4096 * 129) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 130 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0130 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 130)
      (4096 * 130) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 131 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0131 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 131)
      (4096 * 131) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 132 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0132 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 132)
      (4096 * 132) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 133 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0133 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 133)
      (4096 * 133) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 134 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0134 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 134)
      (4096 * 134) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 135 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0135 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 135)
      (4096 * 135) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 136 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0136 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 136)
      (4096 * 136) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 137 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0137 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 137)
      (4096 * 137) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 138 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0138 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 138)
      (4096 * 138) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 139 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0139 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 139)
      (4096 * 139) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 140 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0140 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 140)
      (4096 * 140) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 141 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0141 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 141)
      (4096 * 141) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 142 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0142 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 142)
      (4096 * 142) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 143 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0143 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 143)
      (4096 * 143) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 8 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup008 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 8 + t.val)) (4096 * (16 * 8 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0128
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0129
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0130
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0131
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0132
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0133
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0134
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0135
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0136
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0137
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0138
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0139
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0140
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0141
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0142
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0143

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 144 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0144 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 144)
      (4096 * 144) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 145 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0145 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 145)
      (4096 * 145) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 146 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0146 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 146)
      (4096 * 146) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 147 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0147 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 147)
      (4096 * 147) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 148 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0148 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 148)
      (4096 * 148) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 149 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0149 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 149)
      (4096 * 149) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 150 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0150 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 150)
      (4096 * 150) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 151 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0151 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 151)
      (4096 * 151) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 152 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0152 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 152)
      (4096 * 152) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 153 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0153 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 153)
      (4096 * 153) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 154 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0154 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 154)
      (4096 * 154) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 155 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0155 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 155)
      (4096 * 155) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 156 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0156 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 156)
      (4096 * 156) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 157 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0157 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 157)
      (4096 * 157) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 158 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0158 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 158)
      (4096 * 158) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 159 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0159 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 159)
      (4096 * 159) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 9 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup009 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 9 + t.val)) (4096 * (16 * 9 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0144
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0145
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0146
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0147
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0148
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0149
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0150
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0151
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0152
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0153
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0154
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0155
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0156
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0157
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0158
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0159

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 160 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0160 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 160)
      (4096 * 160) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 161 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0161 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 161)
      (4096 * 161) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 162 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0162 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 162)
      (4096 * 162) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 163 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0163 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 163)
      (4096 * 163) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 164 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0164 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 164)
      (4096 * 164) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 165 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0165 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 165)
      (4096 * 165) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 166 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0166 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 166)
      (4096 * 166) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 167 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0167 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 167)
      (4096 * 167) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 168 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0168 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 168)
      (4096 * 168) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 169 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0169 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 169)
      (4096 * 169) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 170 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0170 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 170)
      (4096 * 170) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 171 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0171 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 171)
      (4096 * 171) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 172 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0172 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 172)
      (4096 * 172) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 173 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0173 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 173)
      (4096 * 173) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 174 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0174 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 174)
      (4096 * 174) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 175 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0175 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 175)
      (4096 * 175) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 10 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup010 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 10 + t.val)) (4096 * (16 * 10 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0160
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0161
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0162
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0163
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0164
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0165
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0166
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0167
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0168
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0169
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0170
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0171
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0172
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0173
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0174
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0175

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 176 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0176 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 176)
      (4096 * 176) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 177 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0177 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 177)
      (4096 * 177) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 178 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0178 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 178)
      (4096 * 178) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 179 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0179 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 179)
      (4096 * 179) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 180 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0180 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 180)
      (4096 * 180) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 181 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0181 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 181)
      (4096 * 181) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 182 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0182 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 182)
      (4096 * 182) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 183 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0183 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 183)
      (4096 * 183) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 184 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0184 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 184)
      (4096 * 184) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 185 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0185 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 185)
      (4096 * 185) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 186 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0186 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 186)
      (4096 * 186) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 187 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0187 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 187)
      (4096 * 187) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 188 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0188 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 188)
      (4096 * 188) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 189 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0189 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 189)
      (4096 * 189) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 190 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0190 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 190)
      (4096 * 190) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 191 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0191 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 191)
      (4096 * 191) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 11 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup011 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 11 + t.val)) (4096 * (16 * 11 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0176
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0177
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0178
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0179
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0180
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0181
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0182
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0183
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0184
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0185
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0186
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0187
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0188
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0189
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0190
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0191

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 192 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0192 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 192)
      (4096 * 192) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 193 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0193 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 193)
      (4096 * 193) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 194 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0194 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 194)
      (4096 * 194) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 195 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0195 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 195)
      (4096 * 195) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 196 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0196 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 196)
      (4096 * 196) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 197 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0197 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 197)
      (4096 * 197) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 198 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0198 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 198)
      (4096 * 198) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 199 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0199 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 199)
      (4096 * 199) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 200 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0200 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 200)
      (4096 * 200) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 201 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0201 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 201)
      (4096 * 201) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 202 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0202 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 202)
      (4096 * 202) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 203 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0203 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 203)
      (4096 * 203) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 204 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0204 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 204)
      (4096 * 204) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 205 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0205 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 205)
      (4096 * 205) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 206 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0206 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 206)
      (4096 * 206) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 207 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0207 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 207)
      (4096 * 207) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 12 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup012 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 12 + t.val)) (4096 * (16 * 12 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0192
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0193
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0194
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0195
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0196
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0197
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0198
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0199
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0200
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0201
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0202
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0203
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0204
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0205
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0206
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0207

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 208 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0208 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 208)
      (4096 * 208) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 209 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0209 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 209)
      (4096 * 209) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 210 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0210 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 210)
      (4096 * 210) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 211 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0211 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 211)
      (4096 * 211) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 212 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0212 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 212)
      (4096 * 212) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 213 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0213 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 213)
      (4096 * 213) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 214 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0214 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 214)
      (4096 * 214) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 215 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0215 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 215)
      (4096 * 215) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 216 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0216 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 216)
      (4096 * 216) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 217 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0217 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 217)
      (4096 * 217) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 218 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0218 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 218)
      (4096 * 218) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 219 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0219 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 219)
      (4096 * 219) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 220 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0220 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 220)
      (4096 * 220) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 221 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0221 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 221)
      (4096 * 221) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 222 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0222 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 222)
      (4096 * 222) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 223 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0223 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 223)
      (4096 * 223) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 13 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup013 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 13 + t.val)) (4096 * (16 * 13 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0208
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0209
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0210
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0211
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0212
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0213
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0214
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0215
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0216
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0217
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0218
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0219
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0220
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0221
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0222
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0223

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 224 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0224 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 224)
      (4096 * 224) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 225 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0225 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 225)
      (4096 * 225) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 226 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0226 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 226)
      (4096 * 226) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 227 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0227 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 227)
      (4096 * 227) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 228 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0228 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 228)
      (4096 * 228) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 229 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0229 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 229)
      (4096 * 229) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 230 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0230 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 230)
      (4096 * 230) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 231 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0231 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 231)
      (4096 * 231) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 232 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0232 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 232)
      (4096 * 232) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 233 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0233 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 233)
      (4096 * 233) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 234 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0234 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 234)
      (4096 * 234) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 235 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0235 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 235)
      (4096 * 235) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 236 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0236 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 236)
      (4096 * 236) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 237 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0237 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 237)
      (4096 * 237) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 238 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0238 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 238)
      (4096 * 238) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 239 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0239 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 239)
      (4096 * 239) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 14 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup014 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 14 + t.val)) (4096 * (16 * 14 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0224
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0225
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0226
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0227
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0228
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0229
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0230
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0231
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0232
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0233
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0234
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0235
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0236
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0237
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0238
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0239

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 240 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0240 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 240)
      (4096 * 240) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 241 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0241 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 241)
      (4096 * 241) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 242 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0242 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 242)
      (4096 * 242) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 243 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0243 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 243)
      (4096 * 243) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 244 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0244 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 244)
      (4096 * 244) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 245 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0245 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 245)
      (4096 * 245) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 246 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0246 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 246)
      (4096 * 246) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 247 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0247 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 247)
      (4096 * 247) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 248 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0248 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 248)
      (4096 * 248) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 249 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0249 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 249)
      (4096 * 249) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 250 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0250 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 250)
      (4096 * 250) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 251 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0251 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 251)
      (4096 * 251) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 252 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0252 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 252)
      (4096 * 252) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 253 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0253 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 253)
      (4096 * 253) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 254 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0254 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 254)
      (4096 * 254) 12 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel evaluation of the 4096 descent obligations of one block.
/-- The descent obligations of block 255 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestBlock0255 :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree 255)
      (4096 * 255) 12 0 = true := by
  decide +kernel

/-- All sixteen blocks of group 15 evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestGroup015 (t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * 15 + t.val)) (4096 * (16 * 15 + t.val)) 12 0 = true := by
  fin_cases t
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0240
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0241
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0242
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0243
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0244
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0245
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0246
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0247
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0248
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0249
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0250
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0251
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0252
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0253
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0254
  · exact generatedAxisGlobalTwelveTwelfthForestBlock0255

/-- All 256 blocks of this shard evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForestShard00 (g t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * (16 * 0 + g.val) + t.val)) (4096 * (16 * (16 * 0 + g.val) + t.val)) 12 0 =
      true := by
  fin_cases g
  · exact generatedAxisGlobalTwelveTwelfthForestGroup000 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup001 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup002 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup003 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup004 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup005 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup006 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup007 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup008 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup009 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup010 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup011 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup012 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup013 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup014 t
  · exact generatedAxisGlobalTwelveTwelfthForestGroup015 t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
