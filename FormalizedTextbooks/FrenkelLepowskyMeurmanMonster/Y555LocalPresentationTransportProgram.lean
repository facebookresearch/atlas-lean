/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Assembly of the kernel-checked chronological source-word reference bounds. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds36
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds37
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds38
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds39
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds40
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds41
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds42
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds43
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds44
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds45
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds46
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramBounds47

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All padded 1024-instruction blocks satisfy the exact chronological reference bounds. -/
theorem y322TransportAllowedBlock (block : Fin 48) (i : Fin 1024) :
    y322TransportAllowedAt (block.val * 1024 + i.val) := by
  fin_cases block
  · exact y322TransportAllowed00 i
  · exact y322TransportAllowed01 i
  · exact y322TransportAllowed02 i
  · exact y322TransportAllowed03 i
  · exact y322TransportAllowed04 i
  · exact y322TransportAllowed05 i
  · exact y322TransportAllowed06 i
  · exact y322TransportAllowed07 i
  · exact y322TransportAllowed08 i
  · exact y322TransportAllowed09 i
  · exact y322TransportAllowed10 i
  · exact y322TransportAllowed11 i
  · exact y322TransportAllowed12 i
  · exact y322TransportAllowed13 i
  · exact y322TransportAllowed14 i
  · exact y322TransportAllowed15 i
  · exact y322TransportAllowed16 i
  · exact y322TransportAllowed17 i
  · exact y322TransportAllowed18 i
  · exact y322TransportAllowed19 i
  · exact y322TransportAllowed20 i
  · exact y322TransportAllowed21 i
  · exact y322TransportAllowed22 i
  · exact y322TransportAllowed23 i
  · exact y322TransportAllowed24 i
  · exact y322TransportAllowed25 i
  · exact y322TransportAllowed26 i
  · exact y322TransportAllowed27 i
  · exact y322TransportAllowed28 i
  · exact y322TransportAllowed29 i
  · exact y322TransportAllowed30 i
  · exact y322TransportAllowed31 i
  · exact y322TransportAllowed32 i
  · exact y322TransportAllowed33 i
  · exact y322TransportAllowed34 i
  · exact y322TransportAllowed35 i
  · exact y322TransportAllowed36 i
  · exact y322TransportAllowed37 i
  · exact y322TransportAllowed38 i
  · exact y322TransportAllowed39 i
  · exact y322TransportAllowed40 i
  · exact y322TransportAllowed41 i
  · exact y322TransportAllowed42 i
  · exact y322TransportAllowed43 i
  · exact y322TransportAllowed44 i
  · exact y322TransportAllowed45 i
  · exact y322TransportAllowed46 i
  · exact y322TransportAllowed47 i

/-- Every actual source-word instruction has only strictly earlier chronological references. -/
theorem y322TransportRaw_allowed (i : Fin 48640) : (y322TransportRaw i).Allowed i.val := by
  let block : Fin 48 := ⟨i.val / 1024, by omega⟩
  let offset : Fin 1024 := ⟨i.val % 1024, Nat.mod_lt _ (by decide)⟩
  have h := y322TransportAllowedBlock block offset
  have he : block.val * 1024 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  rw [he] at h
  simpa only [y322TransportAllowedAt, dite_eq_left i.isLt] using h

/-- The exact chronological H-word and transversal program, now checked acyclic. -/
def y322TransportProgram : Y322WordProgram 48640 :=
  y322RawWordProgram y322TransportRaw y322TransportRaw_allowed

/-- The checked program retains every original chronological raw instruction exactly. -/
theorem y322TransportProgram_raw (i : Fin 48640) :
    y322InstructionRaw (y322TransportProgram i) = y322TransportRaw i :=
  y322RawWordProgram_raw _ _ i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
