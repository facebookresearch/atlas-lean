/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitData
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.IntervalCases

/-! Bounded increasing-code certificates distinguish every actual finite matrix address. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 0 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock000 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨0 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨0 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 1 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock001 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨512 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨512 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 2 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock002 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨1024 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨1024 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 3 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock003 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨1536 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨1536 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 4 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock004 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨2048 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨2048 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 5 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock005 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨2560 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨2560 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 6 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock006 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨3072 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨3072 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 7 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock007 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨3584 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨3584 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 8 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock008 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨4096 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨4096 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 9 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock009 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨4608 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨4608 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 10 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock010 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨5120 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨5120 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 11 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock011 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨5632 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨5632 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 12 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock012 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨6144 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨6144 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 13 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock013 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨6656 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨6656 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 14 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock014 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨7168 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨7168 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 15 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock015 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨7680 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨7680 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 16 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock016 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨8192 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨8192 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 17 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock017 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨8704 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨8704 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 18 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock018 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨9216 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨9216 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 19 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock019 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨9728 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨9728 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 20 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock020 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨10240 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨10240 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 21 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock021 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨10752 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨10752 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 22 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock022 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨11264 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨11264 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 23 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock023 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨11776 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨11776 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 24 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock024 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨12288 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨12288 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 25 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock025 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨12800 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨12800 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 26 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock026 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨13312 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨13312 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 27 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock027 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨13824 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨13824 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 28 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock028 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨14336 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨14336 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 29 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock029 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨14848 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨14848 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 30 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock030 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨15360 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨15360 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 31 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock031 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨15872 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨15872 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 32 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock032 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨16384 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨16384 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 33 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock033 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨16896 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨16896 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 34 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock034 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨17408 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨17408 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 35 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock035 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨17920 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨17920 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 36 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock036 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨18432 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨18432 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 37 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock037 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨18944 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨18944 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 38 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock038 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨19456 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨19456 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 39 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock039 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨19968 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨19968 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 40 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock040 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨20480 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨20480 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 41 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock041 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨20992 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨20992 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 42 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock042 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨21504 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨21504 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 43 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock043 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨22016 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨22016 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 44 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock044 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨22528 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨22528 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 45 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock045 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨23040 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨23040 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 46 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock046 : ∀ n : Fin 512,
    generatedTwelfthGoldenMatrixCode ⟨23552 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨23552 + n.val + 1, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
-- Check one bounded exact portion of adjacent original physical matrix codes.
/-- Every adjacent pair in original code block 47 is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCodeBlock047 : ∀ n : Fin 127,
    generatedTwelfthGoldenMatrixCode ⟨24064 + n.val, by omega⟩ <
      generatedTwelfthGoldenMatrixCode ⟨24064 + n.val + 1, by omega⟩ := by
  decide +kernel

/-- Every adjacent pair of original full matrix codes is strictly increasing. -/
theorem generatedTwelfthGoldenMatrixCode_adjacent (i : Fin 24191) :
    generatedTwelfthGoldenMatrixCode i.castSucc < generatedTwelfthGoldenMatrixCode i.succ := by
  have hb : i.val / 512 < 48 := by omega
  interval_cases hd : i.val / 512
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨0 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨0 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock000 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨512 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨512 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock001 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨1024 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨1024 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock002 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨1536 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨1536 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock003 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨2048 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨2048 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock004 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨2560 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨2560 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock005 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨3072 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨3072 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock006 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨3584 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨3584 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock007 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨4096 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨4096 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock008 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨4608 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨4608 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock009 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨5120 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨5120 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock010 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨5632 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨5632 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock011 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨6144 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨6144 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock012 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨6656 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨6656 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock013 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨7168 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨7168 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock014 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨7680 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨7680 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock015 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨8192 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨8192 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock016 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨8704 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨8704 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock017 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨9216 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨9216 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock018 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨9728 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨9728 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock019 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨10240 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨10240 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock020 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨10752 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨10752 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock021 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨11264 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨11264 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock022 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨11776 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨11776 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock023 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨12288 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨12288 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock024 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨12800 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨12800 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock025 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨13312 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨13312 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock026 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨13824 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨13824 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock027 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨14336 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨14336 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock028 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨14848 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨14848 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock029 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨15360 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨15360 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock030 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨15872 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨15872 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock031 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨16384 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨16384 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock032 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨16896 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨16896 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock033 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨17408 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨17408 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock034 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨17920 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨17920 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock035 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨18432 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨18432 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock036 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨18944 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨18944 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock037 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨19456 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨19456 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock038 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨19968 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨19968 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock039 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨20480 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨20480 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock040 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨20992 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨20992 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock041 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨21504 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨21504 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock042 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨22016 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨22016 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock043 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨22528 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨22528 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock044 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨23040 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨23040 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock045 n
    rwa [hl, hr] at h
  · let n : Fin 512 := ⟨i.val % 512, by omega⟩
    have hl : (⟨23552 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨23552 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock046 n
    rwa [hl, hr] at h
  · let n : Fin 127 := ⟨i.val % 512, by omega⟩
    have hl : (⟨24064 + n.val, by omega⟩ : Fin 24192) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [n]
      omega
    have hr : (⟨24064 + n.val + 1, by omega⟩ : Fin 24192) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp only [n]
      omega
    have h := generatedTwelfthGoldenMatrixCodeBlock047 n
    rwa [hl, hr] at h

/-- Every exact original integer matrix code has a distinct finite address. -/
theorem generatedTwelfthGoldenMatrixCode_injective :
    Function.Injective generatedTwelfthGoldenMatrixCode :=
  (Fin.strictMono_iff_lt_succ.mpr generatedTwelfthGoldenMatrixCode_adjacent).injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
