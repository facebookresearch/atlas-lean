/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortInputData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPacketData10

/-! Full preferred-short destination and phase caches for all eleven genuine compact models. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every source generator uses its own full preferred-short transport cache. -/
def generatedNinthLowerSpinShortTransportWords :
    Fin 11 → Fin 24 → Fin 16 → Fin 16 → ℕ :=
  ![generatedNinthLowerSpinShortTransportWords00,
    generatedNinthLowerSpinShortTransportWords01,
    generatedNinthLowerSpinShortTransportWords02,
    generatedNinthLowerSpinShortTransportWords03,
    generatedNinthLowerSpinShortTransportWords04,
    generatedNinthLowerSpinShortTransportWords05,
    generatedNinthLowerSpinShortTransportWords06,
    generatedNinthLowerSpinShortTransportWords07,
    generatedNinthLowerSpinShortTransportWords08,
    generatedNinthLowerSpinShortTransportWords09,
    generatedNinthLowerSpinShortTransportWords10]

/-- Read the entire eighteen-bit preferred image of one original short coordinate. -/
def generatedNinthLowerSpinShortTransportPacket (i : Fin 11) (r : GriessShortIndex) : ℕ :=
  let a := generatedNinthLowerSpinShortAddress r
  (generatedNinthLowerSpinShortWord (generatedNinthLowerSpinShortTransportWords i) a /
    2 ^ (18 * (a.val % 16))) % 2 ^ 18

/-- Preferred short destination, decoded in the actual original three-family dictionary. -/
def generatedNinthLowerSpinShortDestination (i : Fin 11) (r : GriessShortIndex) :
    GriessShortIndex :=
  generatedNinthLowerSpinShortIndex
    (Fin.ofNat 98280 (generatedNinthLowerSpinShortTransportPacket i r % 2 ^ 17))

/-- The full central sign of the preferred-Q image, including the actual Pauli correction. -/
def generatedNinthLowerSpinShortPhase (i : Fin 11) (r : GriessShortIndex) : ZMod 2 :=
  golayBooleanCast ((generatedNinthLowerSpinShortTransportPacket i r).testBit 17)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
