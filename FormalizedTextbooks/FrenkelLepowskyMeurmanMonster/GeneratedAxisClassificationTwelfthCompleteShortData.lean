/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortInputData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortTransportData11

/-! Every complete original short destination and central phase of the twelve genuine candidates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Each actual candidate retains its complete original preferred short transport packet. -/
def generatedTwelfthCompleteShortTransportWords : Fin 12 → Fin 24 → Fin 16 → Fin 16 → ℕ :=
  ![generatedTwelfthCompleteShortTransportWords00,
    generatedTwelfthCompleteShortTransportWords01,
    generatedTwelfthCompleteShortTransportWords02,
    generatedTwelfthCompleteShortTransportWords03,
    generatedTwelfthCompleteShortTransportWords04,
    generatedTwelfthCompleteShortTransportWords05,
    generatedTwelfthCompleteShortTransportWords06,
    generatedTwelfthCompleteShortTransportWords07,
    generatedTwelfthCompleteShortTransportWords08,
    generatedTwelfthCompleteShortTransportWords09,
    generatedTwelfthCompleteShortTransportWords10,
    generatedTwelfthCompleteShortTransportWords11]

/-- The entire eighteen-bit preferred destination and central sign of an original short row. -/
def generatedTwelfthCompleteShortTransportPacket (g : Fin 12) (r : GriessShortIndex) : ℕ :=
  let a := generatedNinthLowerSpinShortAddress r
  (generatedNinthLowerSpinShortWord (generatedTwelfthCompleteShortTransportWords g) a /
    2 ^ (18 * (a.val % 16))) % 2 ^ 18

/-- The destination is decoded in the unchanged complete original short dictionary. -/
def generatedTwelfthCompleteShortDestination (g : Fin 12) (r : GriessShortIndex) :
    GriessShortIndex :=
  generatedNinthLowerSpinShortIndex
    (Fin.ofNat 98280 (generatedTwelfthCompleteShortTransportPacket g r % 2 ^ 17))

/-- Every preferred short image retains its full central phase. -/
def generatedTwelfthCompleteShortPhase (g : Fin 12) (r : GriessShortIndex) : ZMod 2 :=
  golayBooleanCast ((generatedTwelfthCompleteShortTransportPacket g r).testBit 17)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
