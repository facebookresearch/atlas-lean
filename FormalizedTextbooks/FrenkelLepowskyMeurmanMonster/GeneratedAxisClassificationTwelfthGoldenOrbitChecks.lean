/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck024
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck025
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck026
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck027
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck028
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck031
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck033
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck034
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck035
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck036
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck037
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck038
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck041
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck042
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck043
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck045
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck046
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCheck047
public import Mathlib.Tactic.IntervalCases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitNode

/-! Every exact finite golden-matrix node has its full checked descending source equation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

set_option maxHeartbeats 8000000 in
/-- Every finite original matrix address has the complete checked descending source certificate. -/
theorem generatedTwelfthGoldenOrbit_nodes (n : Fin 24192) :
    generatedTwelfthGoldenOrbitNodeProperty n := by
  have hb : n.val / 512 < 48 := by omega
  interval_cases hd : n.val / 512
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨0 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck000 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨512 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck001 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨1024 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck002 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨1536 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck003 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨2048 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck004 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨2560 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck005 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨3072 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck006 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨3584 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck007 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨4096 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck008 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨4608 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck009 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨5120 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck010 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨5632 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck011 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨6144 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck012 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨6656 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck013 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨7168 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck014 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨7680 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck015 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨8192 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck016 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨8704 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck017 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨9216 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck018 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨9728 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck019 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨10240 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck020 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨10752 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck021 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨11264 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck022 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨11776 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck023 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨12288 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck024 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨12800 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck025 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨13312 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck026 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨13824 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck027 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨14336 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck028 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨14848 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck029 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨15360 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck030 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨15872 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck031 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨16384 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck032 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨16896 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck033 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨17408 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck034 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨17920 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck035 j
    change generatedTwelfthGoldenOrbitNodeProperty ⟨17920 + j.val, by omega⟩ at h
    rwa [hl] at h
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨18432 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck036 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨18944 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck037 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨19456 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck038 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨19968 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck039 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨20480 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck040 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨20992 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck041 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨21504 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck042 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨22016 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck043 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨22528 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck044 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨23040 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck045 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 512 := ⟨n.val % 512, by omega⟩
    have hl : (⟨23552 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck046 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩
  · let j : Fin 128 := ⟨n.val % 512, by omega⟩
    have hl : (⟨24064 + j.val, by omega⟩ : Fin 24192) = n := by
      apply Fin.ext
      dsimp only [j]
      omega
    have h := generatedTwelfthGoldenOrbitCheck047 j
    dsimp only at h
    rw [hl] at h
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
