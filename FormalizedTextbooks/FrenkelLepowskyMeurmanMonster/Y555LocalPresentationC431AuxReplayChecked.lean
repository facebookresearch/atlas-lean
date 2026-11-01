/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Assembly of the unchanged original-source contextual equation replay checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecks28

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Every chronological equation passes the exact source and earlier-context checker. -/
theorem y431AuxReplayProgram_checked (i : Fin 3684) : y431AuxReplayCheckAt i := by
  by_cases h0 : i.val < 128
  · let j : Fin 128 := ⟨i.val - 0, by omega⟩
    have hj : (⟨0 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 0 + (i.val - 0) = i.val
      omega
    have hc := y431AuxReplayChecks00 j
    rw [hj] at hc
    exact hc
  by_cases h1 : i.val < 256
  · let j : Fin 128 := ⟨i.val - 128, by omega⟩
    have hj : (⟨128 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 128 + (i.val - 128) = i.val
      omega
    have hc := y431AuxReplayChecks01 j
    rw [hj] at hc
    exact hc
  by_cases h2 : i.val < 384
  · let j : Fin 128 := ⟨i.val - 256, by omega⟩
    have hj : (⟨256 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 256 + (i.val - 256) = i.val
      omega
    have hc := y431AuxReplayChecks02 j
    rw [hj] at hc
    exact hc
  by_cases h3 : i.val < 512
  · let j : Fin 128 := ⟨i.val - 384, by omega⟩
    have hj : (⟨384 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 384 + (i.val - 384) = i.val
      omega
    have hc := y431AuxReplayChecks03 j
    rw [hj] at hc
    exact hc
  by_cases h4 : i.val < 640
  · let j : Fin 128 := ⟨i.val - 512, by omega⟩
    have hj : (⟨512 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 512 + (i.val - 512) = i.val
      omega
    have hc := y431AuxReplayChecks04 j
    rw [hj] at hc
    exact hc
  by_cases h5 : i.val < 768
  · let j : Fin 128 := ⟨i.val - 640, by omega⟩
    have hj : (⟨640 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 640 + (i.val - 640) = i.val
      omega
    have hc := y431AuxReplayChecks05 j
    rw [hj] at hc
    exact hc
  by_cases h6 : i.val < 896
  · let j : Fin 128 := ⟨i.val - 768, by omega⟩
    have hj : (⟨768 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 768 + (i.val - 768) = i.val
      omega
    have hc := y431AuxReplayChecks06 j
    rw [hj] at hc
    exact hc
  by_cases h7 : i.val < 1024
  · let j : Fin 128 := ⟨i.val - 896, by omega⟩
    have hj : (⟨896 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 896 + (i.val - 896) = i.val
      omega
    have hc := y431AuxReplayChecks07 j
    rw [hj] at hc
    exact hc
  by_cases h8 : i.val < 1152
  · let j : Fin 128 := ⟨i.val - 1024, by omega⟩
    have hj : (⟨1024 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1024 + (i.val - 1024) = i.val
      omega
    have hc := y431AuxReplayChecks08 j
    rw [hj] at hc
    exact hc
  by_cases h9 : i.val < 1280
  · let j : Fin 128 := ⟨i.val - 1152, by omega⟩
    have hj : (⟨1152 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1152 + (i.val - 1152) = i.val
      omega
    have hc := y431AuxReplayChecks09 j
    rw [hj] at hc
    exact hc
  by_cases h10 : i.val < 1408
  · let j : Fin 128 := ⟨i.val - 1280, by omega⟩
    have hj : (⟨1280 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1280 + (i.val - 1280) = i.val
      omega
    have hc := y431AuxReplayChecks10 j
    rw [hj] at hc
    exact hc
  by_cases h11 : i.val < 1536
  · let j : Fin 128 := ⟨i.val - 1408, by omega⟩
    have hj : (⟨1408 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1408 + (i.val - 1408) = i.val
      omega
    have hc := y431AuxReplayChecks11 j
    rw [hj] at hc
    exact hc
  by_cases h12 : i.val < 1664
  · let j : Fin 128 := ⟨i.val - 1536, by omega⟩
    have hj : (⟨1536 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1536 + (i.val - 1536) = i.val
      omega
    have hc := y431AuxReplayChecks12 j
    rw [hj] at hc
    exact hc
  by_cases h13 : i.val < 1792
  · let j : Fin 128 := ⟨i.val - 1664, by omega⟩
    have hj : (⟨1664 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1664 + (i.val - 1664) = i.val
      omega
    have hc := y431AuxReplayChecks13 j
    rw [hj] at hc
    exact hc
  by_cases h14 : i.val < 1920
  · let j : Fin 128 := ⟨i.val - 1792, by omega⟩
    have hj : (⟨1792 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1792 + (i.val - 1792) = i.val
      omega
    have hc := y431AuxReplayChecks14 j
    rw [hj] at hc
    exact hc
  by_cases h15 : i.val < 2048
  · let j : Fin 128 := ⟨i.val - 1920, by omega⟩
    have hj : (⟨1920 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 1920 + (i.val - 1920) = i.val
      omega
    have hc := y431AuxReplayChecks15 j
    rw [hj] at hc
    exact hc
  by_cases h16 : i.val < 2176
  · let j : Fin 128 := ⟨i.val - 2048, by omega⟩
    have hj : (⟨2048 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2048 + (i.val - 2048) = i.val
      omega
    have hc := y431AuxReplayChecks16 j
    rw [hj] at hc
    exact hc
  by_cases h17 : i.val < 2304
  · let j : Fin 128 := ⟨i.val - 2176, by omega⟩
    have hj : (⟨2176 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2176 + (i.val - 2176) = i.val
      omega
    have hc := y431AuxReplayChecks17 j
    rw [hj] at hc
    exact hc
  by_cases h18 : i.val < 2432
  · let j : Fin 128 := ⟨i.val - 2304, by omega⟩
    have hj : (⟨2304 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2304 + (i.val - 2304) = i.val
      omega
    have hc := y431AuxReplayChecks18 j
    rw [hj] at hc
    exact hc
  by_cases h19 : i.val < 2560
  · let j : Fin 128 := ⟨i.val - 2432, by omega⟩
    have hj : (⟨2432 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2432 + (i.val - 2432) = i.val
      omega
    have hc := y431AuxReplayChecks19 j
    rw [hj] at hc
    exact hc
  by_cases h20 : i.val < 2688
  · let j : Fin 128 := ⟨i.val - 2560, by omega⟩
    have hj : (⟨2560 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2560 + (i.val - 2560) = i.val
      omega
    have hc := y431AuxReplayChecks20 j
    rw [hj] at hc
    exact hc
  by_cases h21 : i.val < 2816
  · let j : Fin 128 := ⟨i.val - 2688, by omega⟩
    have hj : (⟨2688 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2688 + (i.val - 2688) = i.val
      omega
    have hc := y431AuxReplayChecks21 j
    rw [hj] at hc
    exact hc
  by_cases h22 : i.val < 2944
  · let j : Fin 128 := ⟨i.val - 2816, by omega⟩
    have hj : (⟨2816 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2816 + (i.val - 2816) = i.val
      omega
    have hc := y431AuxReplayChecks22 j
    rw [hj] at hc
    exact hc
  by_cases h23 : i.val < 3072
  · let j : Fin 128 := ⟨i.val - 2944, by omega⟩
    have hj : (⟨2944 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 2944 + (i.val - 2944) = i.val
      omega
    have hc := y431AuxReplayChecks23 j
    rw [hj] at hc
    exact hc
  by_cases h24 : i.val < 3200
  · let j : Fin 128 := ⟨i.val - 3072, by omega⟩
    have hj : (⟨3072 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 3072 + (i.val - 3072) = i.val
      omega
    have hc := y431AuxReplayChecks24 j
    rw [hj] at hc
    exact hc
  by_cases h25 : i.val < 3328
  · let j : Fin 128 := ⟨i.val - 3200, by omega⟩
    have hj : (⟨3200 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 3200 + (i.val - 3200) = i.val
      omega
    have hc := y431AuxReplayChecks25 j
    rw [hj] at hc
    exact hc
  by_cases h26 : i.val < 3456
  · let j : Fin 128 := ⟨i.val - 3328, by omega⟩
    have hj : (⟨3328 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 3328 + (i.val - 3328) = i.val
      omega
    have hc := y431AuxReplayChecks26 j
    rw [hj] at hc
    exact hc
  by_cases h27 : i.val < 3584
  · let j : Fin 128 := ⟨i.val - 3456, by omega⟩
    have hj : (⟨3456 + j.val, by omega⟩ : Fin 3684) = i := by
      apply Fin.ext
      change 3456 + (i.val - 3456) = i.val
      omega
    have hc := y431AuxReplayChecks27 j
    rw [hj] at hc
    exact hc
  let j : Fin 100 := ⟨i.val - 3584, by omega⟩
  have hj : (⟨3584 + j.val, by omega⟩ : Fin 3684) = i := by
    apply Fin.ext
    change 3584 + (i.val - 3584) = i.val
    omega
  have hc := y431AuxReplayChecks28 j
  rw [hj] at hc
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
