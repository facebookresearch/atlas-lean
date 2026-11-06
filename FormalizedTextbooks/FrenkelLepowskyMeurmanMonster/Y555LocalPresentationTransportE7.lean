/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual E7 subgroup membership of every chronological H transporter word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds36
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Bounds37

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every raw transporter-prefix instruction satisfies its literal source-generator restriction. -/
theorem y322TransportE7AllowedBlock (block : Fin 38) (i : Fin 1024) :
    y322TransportE7AllowedAt (block.val * 1024 + i.val) := by
  fin_cases block
  · exact y322TransportE7Allowed00 i
  · exact y322TransportE7Allowed01 i
  · exact y322TransportE7Allowed02 i
  · exact y322TransportE7Allowed03 i
  · exact y322TransportE7Allowed04 i
  · exact y322TransportE7Allowed05 i
  · exact y322TransportE7Allowed06 i
  · exact y322TransportE7Allowed07 i
  · exact y322TransportE7Allowed08 i
  · exact y322TransportE7Allowed09 i
  · exact y322TransportE7Allowed10 i
  · exact y322TransportE7Allowed11 i
  · exact y322TransportE7Allowed12 i
  · exact y322TransportE7Allowed13 i
  · exact y322TransportE7Allowed14 i
  · exact y322TransportE7Allowed15 i
  · exact y322TransportE7Allowed16 i
  · exact y322TransportE7Allowed17 i
  · exact y322TransportE7Allowed18 i
  · exact y322TransportE7Allowed19 i
  · exact y322TransportE7Allowed20 i
  · exact y322TransportE7Allowed21 i
  · exact y322TransportE7Allowed22 i
  · exact y322TransportE7Allowed23 i
  · exact y322TransportE7Allowed24 i
  · exact y322TransportE7Allowed25 i
  · exact y322TransportE7Allowed26 i
  · exact y322TransportE7Allowed27 i
  · exact y322TransportE7Allowed28 i
  · exact y322TransportE7Allowed29 i
  · exact y322TransportE7Allowed30 i
  · exact y322TransportE7Allowed31 i
  · exact y322TransportE7Allowed32 i
  · exact y322TransportE7Allowed33 i
  · exact y322TransportE7Allowed34 i
  · exact y322TransportE7Allowed35 i
  · exact y322TransportE7Allowed36 i
  · exact y322TransportE7Allowed37 i

/-- The full checked transporter prefix has no source generator outside the genuine E7 subgroup. -/
theorem y322TransportE7Prefix_allowed (i : Fin 48640) (hi : i.val < 38540) :
    (y322InstructionRaw (y322TransportProgram i)).E7Allowed := by
  let block : Fin 38 := ⟨i.val / 1024, by omega⟩
  let offset : Fin 1024 := ⟨i.val % 1024, Nat.mod_lt _ (by decide)⟩
  have h := y322TransportE7AllowedBlock block offset
  have he : block.val * 1024 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  rw [he] at h
  rw [y322TransportProgram_raw]
  simpa only [y322TransportE7AllowedAt, dite_eq_left hi] using h

/-- Every actual H-labelled acyclic transporter word belongs to the original E7 parabolic. -/
theorem y322TransportE7Prefix_mem (i : Fin 48640) (hi : i.val < 38540) :
    y322LocalProgramValue y322TransportProgram i ∈ y322E7Parabolic := by
  exact y322WordProgram_E7_prefix_mem y322TransportProgram y322TransportE7Prefix_allowed i hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
