/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Assembly of the bounded original-source E8 rewrite chunks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8RewriteChecks18

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- The exact global ordering of all checked E8 rewrite chunks. -/
def y431AuxE8RewriteChunk : Fin 1214 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
  fun i =>
  if h : i.val < 64 then
    y431AuxE8RewriteData00 ⟨i.val - 0, by omega⟩
  else
  if h : i.val < 128 then
    y431AuxE8RewriteData01 ⟨i.val - 64, by omega⟩
  else
  if h : i.val < 192 then
    y431AuxE8RewriteData02 ⟨i.val - 128, by omega⟩
  else
  if h : i.val < 256 then
    y431AuxE8RewriteData03 ⟨i.val - 192, by omega⟩
  else
  if h : i.val < 320 then
    y431AuxE8RewriteData04 ⟨i.val - 256, by omega⟩
  else
  if h : i.val < 384 then
    y431AuxE8RewriteData05 ⟨i.val - 320, by omega⟩
  else
  if h : i.val < 448 then
    y431AuxE8RewriteData06 ⟨i.val - 384, by omega⟩
  else
  if h : i.val < 512 then
    y431AuxE8RewriteData07 ⟨i.val - 448, by omega⟩
  else
  if h : i.val < 576 then
    y431AuxE8RewriteData08 ⟨i.val - 512, by omega⟩
  else
  if h : i.val < 640 then
    y431AuxE8RewriteData09 ⟨i.val - 576, by omega⟩
  else
  if h : i.val < 704 then
    y431AuxE8RewriteData10 ⟨i.val - 640, by omega⟩
  else
  if h : i.val < 768 then
    y431AuxE8RewriteData11 ⟨i.val - 704, by omega⟩
  else
  if h : i.val < 832 then
    y431AuxE8RewriteData12 ⟨i.val - 768, by omega⟩
  else
  if h : i.val < 896 then
    y431AuxE8RewriteData13 ⟨i.val - 832, by omega⟩
  else
  if h : i.val < 960 then
    y431AuxE8RewriteData14 ⟨i.val - 896, by omega⟩
  else
  if h : i.val < 1024 then
    y431AuxE8RewriteData15 ⟨i.val - 960, by omega⟩
  else
  if h : i.val < 1088 then
    y431AuxE8RewriteData16 ⟨i.val - 1024, by omega⟩
  else
  if h : i.val < 1152 then
    y431AuxE8RewriteData17 ⟨i.val - 1088, by omega⟩
  else
    y431AuxE8RewriteData18 ⟨i.val - 1152, by omega⟩

set_option maxRecDepth 100000 in
/-- All global chunks pass the original C431 Coxeter checker by their bounded block proofs. -/
theorem y431AuxE8RewriteChunk_checked (i : Fin 1214) :
    y431CoxeterRun (y431AuxE8RewriteChunk i).2.2 (y431AuxE8RewriteChunk i).1 =
      some (y431AuxE8RewriteChunk i).2.1 := by
  by_cases h0 : i.val < 64
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData00 ⟨i.val - 0, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_left h0]
    rw [hi]
    exact y431AuxE8RewriteChecks00 _
  by_cases h1 : i.val < 128
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData01 ⟨i.val - 64, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_left h1]
    rw [hi]
    exact y431AuxE8RewriteChecks01 _
  by_cases h2 : i.val < 192
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData02 ⟨i.val - 128, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_left h2]
    rw [hi]
    exact y431AuxE8RewriteChecks02 _
  by_cases h3 : i.val < 256
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData03 ⟨i.val - 192, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
    rw [hi]
    exact y431AuxE8RewriteChecks03 _
  by_cases h4 : i.val < 320
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData04 ⟨i.val - 256, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_left h4]
    rw [hi]
    exact y431AuxE8RewriteChecks04 _
  by_cases h5 : i.val < 384
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData05 ⟨i.val - 320, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_left h5]
    rw [hi]
    exact y431AuxE8RewriteChecks05 _
  by_cases h6 : i.val < 448
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData06 ⟨i.val - 384, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_left h6]
    rw [hi]
    exact y431AuxE8RewriteChecks06 _
  by_cases h7 : i.val < 512
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData07 ⟨i.val - 448, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_left h7]
    rw [hi]
    exact y431AuxE8RewriteChecks07 _
  by_cases h8 : i.val < 576
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData08 ⟨i.val - 512, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_left h8]
    rw [hi]
    exact y431AuxE8RewriteChecks08 _
  by_cases h9 : i.val < 640
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData09 ⟨i.val - 576, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_left h9]
    rw [hi]
    exact y431AuxE8RewriteChecks09 _
  by_cases h10 : i.val < 704
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData10 ⟨i.val - 640, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_left h10]
    rw [hi]
    exact y431AuxE8RewriteChecks10 _
  by_cases h11 : i.val < 768
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData11 ⟨i.val - 704, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_left h11]
    rw [hi]
    exact y431AuxE8RewriteChecks11 _
  by_cases h12 : i.val < 832
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData12 ⟨i.val - 768, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_left h12]
    rw [hi]
    exact y431AuxE8RewriteChecks12 _
  by_cases h13 : i.val < 896
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData13 ⟨i.val - 832, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_left h13]
    rw [hi]
    exact y431AuxE8RewriteChecks13 _
  by_cases h14 : i.val < 960
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData14 ⟨i.val - 896, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_left h14]
    rw [hi]
    exact y431AuxE8RewriteChecks14 _
  by_cases h15 : i.val < 1024
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData15 ⟨i.val - 960, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_left h15]
    rw [hi]
    exact y431AuxE8RewriteChecks15 _
  by_cases h16 : i.val < 1088
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData16 ⟨i.val - 1024, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_left h16]
    rw [hi]
    exact y431AuxE8RewriteChecks16 _
  by_cases h17 : i.val < 1152
  · have hi : y431AuxE8RewriteChunk i =
        y431AuxE8RewriteData17 ⟨i.val - 1088, by omega⟩ := by
      unfold y431AuxE8RewriteChunk
      rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
        dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
        dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
        dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
        dite_eq_right h16, dite_eq_left h17]
    rw [hi]
    exact y431AuxE8RewriteChecks17 _
  have hi : y431AuxE8RewriteChunk i =
      y431AuxE8RewriteData18 ⟨i.val - 1152, by omega⟩ := by
    unfold y431AuxE8RewriteChunk
    rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
      dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
      dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
      dite_eq_right h12, dite_eq_right h13, dite_eq_right h14, dite_eq_right h15,
      dite_eq_right h16, dite_eq_right h17]
  rw [hi]
  exact y431AuxE8RewriteChecks18 _

/-- Every global literal chunk preserves the actual original C431 group element. -/
theorem y431AuxE8RewriteChunk_valid (i : Fin 1214) :
    y431PositiveWord (y431AuxE8RewriteChunk i).1 =
      y431PositiveWord (y431AuxE8RewriteChunk i).2.1 :=
  y431CoxeterRun_valid _ _ _ (y431AuxE8RewriteChunk_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
