/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact acyclic equation program for the original-source redundant-symbol C431 replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayBounds28

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000

/-- The exact chronological raw certificate table, with every literal instruction retained. -/
def y431AuxReplayRawData (i : Fin 3684) : Y322RawContextCertificate :=
  if h : i.val < 128 then
    y431AuxReplayData00 ⟨i.val - 0, by omega⟩
  else
  if h : i.val < 256 then
    y431AuxReplayData01 ⟨i.val - 128, by omega⟩
  else
  if h : i.val < 384 then
    y431AuxReplayData02 ⟨i.val - 256, by omega⟩
  else
  if h : i.val < 512 then
    y431AuxReplayData03 ⟨i.val - 384, by omega⟩
  else
  if h : i.val < 640 then
    y431AuxReplayData04 ⟨i.val - 512, by omega⟩
  else
  if h : i.val < 768 then
    y431AuxReplayData05 ⟨i.val - 640, by omega⟩
  else
  if h : i.val < 896 then
    y431AuxReplayData06 ⟨i.val - 768, by omega⟩
  else
  if h : i.val < 1024 then
    y431AuxReplayData07 ⟨i.val - 896, by omega⟩
  else
  if h : i.val < 1152 then
    y431AuxReplayData08 ⟨i.val - 1024, by omega⟩
  else
  if h : i.val < 1280 then
    y431AuxReplayData09 ⟨i.val - 1152, by omega⟩
  else
  if h : i.val < 1408 then
    y431AuxReplayData10 ⟨i.val - 1280, by omega⟩
  else
  if h : i.val < 1536 then
    y431AuxReplayData11 ⟨i.val - 1408, by omega⟩
  else
  if h : i.val < 1664 then
    y431AuxReplayData12 ⟨i.val - 1536, by omega⟩
  else
  if h : i.val < 1792 then
    y431AuxReplayData13 ⟨i.val - 1664, by omega⟩
  else
  if h : i.val < 1920 then
    y431AuxReplayData14 ⟨i.val - 1792, by omega⟩
  else
  if h : i.val < 2048 then
    y431AuxReplayData15 ⟨i.val - 1920, by omega⟩
  else
  if h : i.val < 2176 then
    y431AuxReplayData16 ⟨i.val - 2048, by omega⟩
  else
  if h : i.val < 2304 then
    y431AuxReplayData17 ⟨i.val - 2176, by omega⟩
  else
  if h : i.val < 2432 then
    y431AuxReplayData18 ⟨i.val - 2304, by omega⟩
  else
  if h : i.val < 2560 then
    y431AuxReplayData19 ⟨i.val - 2432, by omega⟩
  else
  if h : i.val < 2688 then
    y431AuxReplayData20 ⟨i.val - 2560, by omega⟩
  else
  if h : i.val < 2816 then
    y431AuxReplayData21 ⟨i.val - 2688, by omega⟩
  else
  if h : i.val < 2944 then
    y431AuxReplayData22 ⟨i.val - 2816, by omega⟩
  else
  if h : i.val < 3072 then
    y431AuxReplayData23 ⟨i.val - 2944, by omega⟩
  else
  if h : i.val < 3200 then
    y431AuxReplayData24 ⟨i.val - 3072, by omega⟩
  else
  if h : i.val < 3328 then
    y431AuxReplayData25 ⟨i.val - 3200, by omega⟩
  else
  if h : i.val < 3456 then
    y431AuxReplayData26 ⟨i.val - 3328, by omega⟩
  else
  if h : i.val < 3584 then
    y431AuxReplayData27 ⟨i.val - 3456, by omega⟩
  else
    y431AuxReplayData28 ⟨i.val - 3584, by omega⟩

/-- Every literal instruction satisfies its actual alphabet, source and chronological bounds. -/
theorem y431AuxReplayRawData_allowed (i : Fin 3684) :
    (y431AuxReplayRawData i).Allowed 810 856 i.val := by
  by_cases h0 : i.val < 128
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData00 ⟨i.val, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_left h0]
      apply congrArg y431AuxReplayData00
      apply Fin.ext
      change i.val - 0 = i.val
      exact Nat.sub_zero i.val
    rw [hl]
    have hb := y431AuxReplayBounds00 (⟨i.val, by omega⟩ : Fin 128)
    simpa only [Fin.val_mk, Nat.zero_add] using hb
  by_cases h1 : i.val < 256
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData01 ⟨i.val - 128, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_left h1]
    rw [hl]
    have hb := y431AuxReplayBounds01 (⟨i.val - 128, by omega⟩ : Fin 128)
    have hi : 128 + (i.val - 128) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h2 : i.val < 384
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData02 ⟨i.val - 256, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_left h2]
    rw [hl]
    have hb := y431AuxReplayBounds02 (⟨i.val - 256, by omega⟩ : Fin 128)
    have hi : 256 + (i.val - 256) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h3 : i.val < 512
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData03 ⟨i.val - 384, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
    rw [hl]
    have hb := y431AuxReplayBounds03 (⟨i.val - 384, by omega⟩ : Fin 128)
    have hi : 384 + (i.val - 384) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h4 : i.val < 640
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData04 ⟨i.val - 512, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_left h4]
    rw [hl]
    have hb := y431AuxReplayBounds04 (⟨i.val - 512, by omega⟩ : Fin 128)
    have hi : 512 + (i.val - 512) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h5 : i.val < 768
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData05 ⟨i.val - 640, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_left h5]
    rw [hl]
    have hb := y431AuxReplayBounds05 (⟨i.val - 640, by omega⟩ : Fin 128)
    have hi : 640 + (i.val - 640) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h6 : i.val < 896
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData06 ⟨i.val - 768, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_left h6]
    rw [hl]
    have hb := y431AuxReplayBounds06 (⟨i.val - 768, by omega⟩ : Fin 128)
    have hi : 768 + (i.val - 768) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h7 : i.val < 1024
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData07 ⟨i.val - 896, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_left h7]
    rw [hl]
    have hb := y431AuxReplayBounds07 (⟨i.val - 896, by omega⟩ : Fin 128)
    have hi : 896 + (i.val - 896) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h8 : i.val < 1152
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData08 ⟨i.val - 1024, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_left h8]
    rw [hl]
    have hb := y431AuxReplayBounds08 (⟨i.val - 1024, by omega⟩ : Fin 128)
    have hi : 1024 + (i.val - 1024) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h9 : i.val < 1280
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData09 ⟨i.val - 1152, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_left h9]
    rw [hl]
    have hb := y431AuxReplayBounds09 (⟨i.val - 1152, by omega⟩ : Fin 128)
    have hi : 1152 + (i.val - 1152) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h10 : i.val < 1408
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData10 ⟨i.val - 1280, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_left h10]
    rw [hl]
    have hb := y431AuxReplayBounds10 (⟨i.val - 1280, by omega⟩ : Fin 128)
    have hi : 1280 + (i.val - 1280) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h11 : i.val < 1536
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData11 ⟨i.val - 1408, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_left h11]
    rw [hl]
    have hb := y431AuxReplayBounds11 (⟨i.val - 1408, by omega⟩ : Fin 128)
    have hi : 1408 + (i.val - 1408) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h12 : i.val < 1664
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData12 ⟨i.val - 1536, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_left h12]
    rw [hl]
    have hb := y431AuxReplayBounds12 (⟨i.val - 1536, by omega⟩ : Fin 128)
    have hi : 1536 + (i.val - 1536) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h13 : i.val < 1792
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData13 ⟨i.val - 1664, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_left h13]
    rw [hl]
    have hb := y431AuxReplayBounds13 (⟨i.val - 1664, by omega⟩ : Fin 128)
    have hi : 1664 + (i.val - 1664) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h14 : i.val < 1920
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData14 ⟨i.val - 1792, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_left h14]
    rw [hl]
    have hb := y431AuxReplayBounds14 (⟨i.val - 1792, by omega⟩ : Fin 128)
    have hi : 1792 + (i.val - 1792) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h15 : i.val < 2048
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData15 ⟨i.val - 1920, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_left h15]
    rw [hl]
    have hb := y431AuxReplayBounds15 (⟨i.val - 1920, by omega⟩ : Fin 128)
    have hi : 1920 + (i.val - 1920) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h16 : i.val < 2176
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData16 ⟨i.val - 2048, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_left h16]
    rw [hl]
    have hb := y431AuxReplayBounds16 (⟨i.val - 2048, by omega⟩ : Fin 128)
    have hi : 2048 + (i.val - 2048) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h17 : i.val < 2304
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData17 ⟨i.val - 2176, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_left h17]
    rw [hl]
    have hb := y431AuxReplayBounds17 (⟨i.val - 2176, by omega⟩ : Fin 128)
    have hi : 2176 + (i.val - 2176) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h18 : i.val < 2432
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData18 ⟨i.val - 2304, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_left h18]
    rw [hl]
    have hb := y431AuxReplayBounds18 (⟨i.val - 2304, by omega⟩ : Fin 128)
    have hi : 2304 + (i.val - 2304) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h19 : i.val < 2560
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData19 ⟨i.val - 2432, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_left h19]
    rw [hl]
    have hb := y431AuxReplayBounds19 (⟨i.val - 2432, by omega⟩ : Fin 128)
    have hi : 2432 + (i.val - 2432) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h20 : i.val < 2688
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData20 ⟨i.val - 2560, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_left h20]
    rw [hl]
    have hb := y431AuxReplayBounds20 (⟨i.val - 2560, by omega⟩ : Fin 128)
    have hi : 2560 + (i.val - 2560) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h21 : i.val < 2816
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData21 ⟨i.val - 2688, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_left h21]
    rw [hl]
    have hb := y431AuxReplayBounds21 (⟨i.val - 2688, by omega⟩ : Fin 128)
    have hi : 2688 + (i.val - 2688) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h22 : i.val < 2944
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData22 ⟨i.val - 2816, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_right h21, dite_eq_left h22]
    rw [hl]
    have hb := y431AuxReplayBounds22 (⟨i.val - 2816, by omega⟩ : Fin 128)
    have hi : 2816 + (i.val - 2816) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h23 : i.val < 3072
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData23 ⟨i.val - 2944, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_right h21, dite_eq_right h22, dite_eq_left h23]
    rw [hl]
    have hb := y431AuxReplayBounds23 (⟨i.val - 2944, by omega⟩ : Fin 128)
    have hi : 2944 + (i.val - 2944) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h24 : i.val < 3200
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData24 ⟨i.val - 3072, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_right h21, dite_eq_right h22, dite_eq_right h23,
        dite_eq_left h24]
    rw [hl]
    have hb := y431AuxReplayBounds24 (⟨i.val - 3072, by omega⟩ : Fin 128)
    have hi : 3072 + (i.val - 3072) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h25 : i.val < 3328
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData25 ⟨i.val - 3200, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_right h21, dite_eq_right h22, dite_eq_right h23,
        dite_eq_right h24, dite_eq_left h25]
    rw [hl]
    have hb := y431AuxReplayBounds25 (⟨i.val - 3200, by omega⟩ : Fin 128)
    have hi : 3200 + (i.val - 3200) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h26 : i.val < 3456
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData26 ⟨i.val - 3328, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_right h21, dite_eq_right h22, dite_eq_right h23,
        dite_eq_right h24, dite_eq_right h25, dite_eq_left h26]
    rw [hl]
    have hb := y431AuxReplayBounds26 (⟨i.val - 3328, by omega⟩ : Fin 128)
    have hi : 3328 + (i.val - 3328) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  by_cases h27 : i.val < 3584
  · have hl : y431AuxReplayRawData i =
        y431AuxReplayData27 ⟨i.val - 3456, by omega⟩ := by
      unfold y431AuxReplayRawData
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
        dite_eq_right h20, dite_eq_right h21, dite_eq_right h22, dite_eq_right h23,
        dite_eq_right h24, dite_eq_right h25, dite_eq_right h26, dite_eq_left h27]
    rw [hl]
    have hb := y431AuxReplayBounds27 (⟨i.val - 3456, by omega⟩ : Fin 128)
    have hi : 3456 + (i.val - 3456) = i.val := by omega
    simpa only [Fin.val_mk, hi] using hb
  have hl : y431AuxReplayRawData i =
      y431AuxReplayData28 ⟨i.val - 3584, by omega⟩ := by
    unfold y431AuxReplayRawData
    rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
      dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
      dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
      dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
      dite_eq_right h16, dite_eq_right h17, dite_eq_right h18, dite_eq_right h19,
      dite_eq_right h20, dite_eq_right h21, dite_eq_right h22, dite_eq_right h23,
      dite_eq_right h24, dite_eq_right h25, dite_eq_right h26, dite_eq_right h27]
  rw [hl]
  have hb := y431AuxReplayBounds28 (⟨i.val - 3584, by omega⟩ : Fin 100)
  have hi : 3584 + (i.val - 3584) = i.val := by omega
  simpa only [Fin.val_mk, hi] using hb

/-- Decode the original literal table only after checking all its exact chronological bounds. -/
def y431AuxReplayProgram : Y322ContextEquationProgram (Fin 810) (Fin 856) 3684 :=
  y322RawContextProgram 810 856 y431AuxReplayRawData y431AuxReplayRawData_allowed

/-- The literal source equations are the explicitly numbered first eight hundred fifty-six rows. -/
def y431AuxReplaySourceEquation (i : Fin 856) : Y322WordEquation (Fin 810) :=
  (y431AuxReplayProgram ⟨i.val, by omega⟩).1

/-- The unchanged contextual checker applied at an actual finite chronological row. -/
def y431AuxReplayCheckAt (i : Fin 3684) : Prop :=
  y322ContextEquationProgramChecked y431AuxReplaySourceEquation y431AuxReplayProgram i

/-- Actual literal-source and prior-equation replay is decidable at every bounded row. -/
instance y431AuxReplayCheckAtDecidable (i : Fin 3684) : Decidable (y431AuxReplayCheckAt i) := by
  unfold y431AuxReplayCheckAt y322ContextEquationProgramChecked
  split
  · unfold y322EquationsSameReduction
    infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
