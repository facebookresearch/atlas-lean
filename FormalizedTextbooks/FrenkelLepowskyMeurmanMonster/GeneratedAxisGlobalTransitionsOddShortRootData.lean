/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootMaskCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot01Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot01Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot01Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot03Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot03Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot03Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot04Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot04Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot04Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot05Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot05Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot05Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot06Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot06Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot06Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Batch02Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot08Batch00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot08Batch01Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot08Batch02Data

/-! Candidate entire signed preferred-short packets for all nine original odd-family roots. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster


/-- Exact original pair input of each of the 552 preferred packet entries. -/
def generatedAxisGlobalOddShortInput (n : Fin 552) : GeneratedAxisGlobalOddShortPacketIndex :=
  (⟨n.val / 276, by omega⟩, ⟨n.val % 276, Nat.mod_lt _ (by decide)⟩)

/-- Three bounded packet batches enumerate every original entry and retain harmless padding. -/
def generatedAxisGlobalOddShortBatchNumber (b : Fin 3) (i : Fin 256) : Fin 552 :=
  ⟨(256 * b.val + i.val) % 552, Nat.mod_lt _ (by decide)⟩

/-- All separately stored original candidate label batches. -/
def generatedAxisGlobalOddShortRootLabelBatches : Fin 9 → Fin 3 → Fin 256 → GriessShortIndex :=
  ![![generatedAxisGlobalOddShortRoot00Batch00Label,
      generatedAxisGlobalOddShortRoot00Batch01Label,
      generatedAxisGlobalOddShortRoot00Batch02Label],
    ![generatedAxisGlobalOddShortRoot01Batch00Label,
      generatedAxisGlobalOddShortRoot01Batch01Label,
      generatedAxisGlobalOddShortRoot01Batch02Label],
    ![generatedAxisGlobalOddShortRoot02Batch00Label,
      generatedAxisGlobalOddShortRoot02Batch01Label,
      generatedAxisGlobalOddShortRoot02Batch02Label],
    ![generatedAxisGlobalOddShortRoot03Batch00Label,
      generatedAxisGlobalOddShortRoot03Batch01Label,
      generatedAxisGlobalOddShortRoot03Batch02Label],
    ![generatedAxisGlobalOddShortRoot04Batch00Label,
      generatedAxisGlobalOddShortRoot04Batch01Label,
      generatedAxisGlobalOddShortRoot04Batch02Label],
    ![generatedAxisGlobalOddShortRoot05Batch00Label,
      generatedAxisGlobalOddShortRoot05Batch01Label,
      generatedAxisGlobalOddShortRoot05Batch02Label],
    ![generatedAxisGlobalOddShortRoot06Batch00Label,
      generatedAxisGlobalOddShortRoot06Batch01Label,
      generatedAxisGlobalOddShortRoot06Batch02Label],
    ![generatedAxisGlobalOddShortRoot07Batch00Label,
      generatedAxisGlobalOddShortRoot07Batch01Label,
      generatedAxisGlobalOddShortRoot07Batch02Label],
    ![generatedAxisGlobalOddShortRoot08Batch00Label,
      generatedAxisGlobalOddShortRoot08Batch01Label,
      generatedAxisGlobalOddShortRoot08Batch02Label]]

/-- The exact candidate original label at every preferred input number. -/
def generatedAxisGlobalOddShortRootLabels (k : Fin 9) (n : Fin 552) : GriessShortIndex :=
  generatedAxisGlobalOddShortRootLabelBatches k ⟨n.val / 256, by omega⟩
    ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- All separately stored original candidate phase batches. -/
def generatedAxisGlobalOddShortRootPhaseBatches : Fin 9 → Fin 3 → Fin 256 → ZMod 2 :=
  ![![generatedAxisGlobalOddShortRoot00Batch00Phase,
      generatedAxisGlobalOddShortRoot00Batch01Phase,
      generatedAxisGlobalOddShortRoot00Batch02Phase],
    ![generatedAxisGlobalOddShortRoot01Batch00Phase,
      generatedAxisGlobalOddShortRoot01Batch01Phase,
      generatedAxisGlobalOddShortRoot01Batch02Phase],
    ![generatedAxisGlobalOddShortRoot02Batch00Phase,
      generatedAxisGlobalOddShortRoot02Batch01Phase,
      generatedAxisGlobalOddShortRoot02Batch02Phase],
    ![generatedAxisGlobalOddShortRoot03Batch00Phase,
      generatedAxisGlobalOddShortRoot03Batch01Phase,
      generatedAxisGlobalOddShortRoot03Batch02Phase],
    ![generatedAxisGlobalOddShortRoot04Batch00Phase,
      generatedAxisGlobalOddShortRoot04Batch01Phase,
      generatedAxisGlobalOddShortRoot04Batch02Phase],
    ![generatedAxisGlobalOddShortRoot05Batch00Phase,
      generatedAxisGlobalOddShortRoot05Batch01Phase,
      generatedAxisGlobalOddShortRoot05Batch02Phase],
    ![generatedAxisGlobalOddShortRoot06Batch00Phase,
      generatedAxisGlobalOddShortRoot06Batch01Phase,
      generatedAxisGlobalOddShortRoot06Batch02Phase],
    ![generatedAxisGlobalOddShortRoot07Batch00Phase,
      generatedAxisGlobalOddShortRoot07Batch01Phase,
      generatedAxisGlobalOddShortRoot07Batch02Phase],
    ![generatedAxisGlobalOddShortRoot08Batch00Phase,
      generatedAxisGlobalOddShortRoot08Batch01Phase,
      generatedAxisGlobalOddShortRoot08Batch02Phase]]

/-- The exact candidate original phase at every preferred input number. -/
def generatedAxisGlobalOddShortRootPhases (k : Fin 9) (n : Fin 552) : ZMod 2 :=
  generatedAxisGlobalOddShortRootPhaseBatches k ⟨n.val / 256, by omega⟩
    ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
