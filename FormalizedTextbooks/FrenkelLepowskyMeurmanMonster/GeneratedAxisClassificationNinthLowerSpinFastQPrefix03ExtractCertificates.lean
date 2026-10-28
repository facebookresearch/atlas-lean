/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQPrefix03ExtractData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQPrefix48Extract

/-! Whole source-prefix extraction replaces repeated long-array evaluation exactly. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem getD_extract_of_bounds (xs : Array ℕ)
    (start stop j : ℕ) (hj : j < min stop xs.size - start) :
    (xs.extract start stop).getD j 0 = xs.getD (start + j) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, hj, ite_true]

/-- An exact full slice transfers all24 original source reads without replaying that source. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_slice_function (xs small : Array ℕ)
    (start : ℕ) (hsize : small.size = 24)
    (hslice : xs.extract start (start + 24) = small) :
    (fun j : Fin 24 => xs.getD (start + j.val) 0) =
      (fun j : Fin 24 => small.getD j.val 0) := by
  have hs : min (start + 24) xs.size - start = 24 := by
    have h := congrArg Array.size hslice
    simpa only [Array.size_extract, hsize] using h
  funext j
  have hj : j.val < min (start + 24) xs.size - start := by
    rw [hs]
    exact j.isLt
  rw [← getD_extract_of_bounds xs start (start + 24) j.val hj, hslice]

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_048 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1152 1176 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 0 := by
  exact generatedNinth_lower_spin_fast_q_prefix48_extract

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_048 :
    generatedNinthLowerSpinSourceQReplayWord 0 48 =
      generatedNinthLowerSpinFastQPrefix03 0 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 0) 1152
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 0)
    generatedNinth_lower_spin_fast_q_prefix03_extract_048
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1152 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 0 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 0 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_049 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1176 1200 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_049 :
    generatedNinthLowerSpinSourceQReplayWord 0 49 =
      generatedNinthLowerSpinFastQPrefix03 1 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 1) 1176
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 1)
    generatedNinth_lower_spin_fast_q_prefix03_extract_049
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1176 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 1 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 1 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_050 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1200 1224 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_050 :
    generatedNinthLowerSpinSourceQReplayWord 0 50 =
      generatedNinthLowerSpinFastQPrefix03 2 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 2) 1200
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 2)
    generatedNinth_lower_spin_fast_q_prefix03_extract_050
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1200 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 2 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 2 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_051 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1224 1248 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_051 :
    generatedNinthLowerSpinSourceQReplayWord 0 51 =
      generatedNinthLowerSpinFastQPrefix03 3 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 3) 1224
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 3)
    generatedNinth_lower_spin_fast_q_prefix03_extract_051
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1224 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 3 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 3 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_052 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1248 1272 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_052 :
    generatedNinthLowerSpinSourceQReplayWord 0 52 =
      generatedNinthLowerSpinFastQPrefix03 4 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 4) 1248
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 4)
    generatedNinth_lower_spin_fast_q_prefix03_extract_052
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1248 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 4 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 4 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_053 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1272 1296 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_053 :
    generatedNinthLowerSpinSourceQReplayWord 0 53 =
      generatedNinthLowerSpinFastQPrefix03 5 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 5) 1272
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 5)
    generatedNinth_lower_spin_fast_q_prefix03_extract_053
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1272 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 5 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 5 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_054 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1296 1320 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_054 :
    generatedNinthLowerSpinSourceQReplayWord 0 54 =
      generatedNinthLowerSpinFastQPrefix03 6 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 6) 1296
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 6)
    generatedNinth_lower_spin_fast_q_prefix03_extract_054
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1296 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 6 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 6 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_055 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1320 1344 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_055 :
    generatedNinthLowerSpinSourceQReplayWord 0 55 =
      generatedNinthLowerSpinFastQPrefix03 7 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 7) 1320
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 7)
    generatedNinth_lower_spin_fast_q_prefix03_extract_055
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1320 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 7 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 7 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_056 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1344 1368 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_056 :
    generatedNinthLowerSpinSourceQReplayWord 0 56 =
      generatedNinthLowerSpinFastQPrefix03 8 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 8) 1344
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 8)
    generatedNinth_lower_spin_fast_q_prefix03_extract_056
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1344 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 8 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 8 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_057 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1368 1392 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_057 :
    generatedNinthLowerSpinSourceQReplayWord 0 57 =
      generatedNinthLowerSpinFastQPrefix03 9 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 9) 1368
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 9)
    generatedNinth_lower_spin_fast_q_prefix03_extract_057
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1368 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 9 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 9 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_058 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1392 1416 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_058 :
    generatedNinthLowerSpinSourceQReplayWord 0 58 =
      generatedNinthLowerSpinFastQPrefix03 10 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 10) 1392
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 10)
    generatedNinth_lower_spin_fast_q_prefix03_extract_058
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1392 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 10 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 10 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_059 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1416 1440 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_059 :
    generatedNinthLowerSpinSourceQReplayWord 0 59 =
      generatedNinthLowerSpinFastQPrefix03 11 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 11) 1416
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 11)
    generatedNinth_lower_spin_fast_q_prefix03_extract_059
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1416 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 11 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 11 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_060 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1440 1464 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_060 :
    generatedNinthLowerSpinSourceQReplayWord 0 60 =
      generatedNinthLowerSpinFastQPrefix03 12 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 12) 1440
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 12)
    generatedNinth_lower_spin_fast_q_prefix03_extract_060
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1440 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 12 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 12 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_061 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1464 1488 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_061 :
    generatedNinthLowerSpinSourceQReplayWord 0 61 =
      generatedNinthLowerSpinFastQPrefix03 13 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 13) 1464
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 13)
    generatedNinth_lower_spin_fast_q_prefix03_extract_061
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1464 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 13 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 13 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_062 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1488 1512 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_062 :
    generatedNinthLowerSpinSourceQReplayWord 0 62 =
      generatedNinthLowerSpinFastQPrefix03 14 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 14) 1488
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 14)
    generatedNinth_lower_spin_fast_q_prefix03_extract_062
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1488 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 14 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 14 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_063 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1512 1536 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_063 :
    generatedNinthLowerSpinSourceQReplayWord 0 63 =
      generatedNinthLowerSpinFastQPrefix03 15 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 15) 1512
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 15)
    generatedNinth_lower_spin_fast_q_prefix03_extract_063
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1512 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 15 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 15 j)

set_option maxHeartbeats 8000000 in
-- Reduce this one exact full source slice through a single list drop and take.
/-- The small array is the original complete source slice, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_064 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1536 1560 =
      generatedNinthLowerSpinFastQPrefix03ExtractArrays 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- This entire original prefix function retains every actual central coordinate. -/
theorem generatedNinth_lower_spin_fast_q_prefix03_extract_function_064 :
    generatedNinthLowerSpinSourceQReplayWord 0 64 =
      generatedNinthLowerSpinFastQPrefix03 16 := by
  have h := generatedNinth_lower_spin_fast_q_prefix03_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinFastQPrefix03ExtractArrays 16) 1536
    (generatedNinth_lower_spin_fast_q_prefix03_extract_sizes 16)
    generatedNinth_lower_spin_fast_q_prefix03_extract_064
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1536 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 16 j
  exact (congrFun h j).trans
    (generatedNinth_lower_spin_fast_q_prefix03_extract_values 16 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
