/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded13
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded14
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded15
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortEncoded16

/-! Complete actual real short-coordinate transport of the fifth root-zero normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All checked batch outputs, indexed by their exact finite packet numbers. -/
def generatedAxisGlobalFifthRoot00ShortLabels : Fin 17 → Fin 256 → GriessShortIndex :=
  ![generatedAxisGlobalFifthRoot00Short00Label,
    generatedAxisGlobalFifthRoot00Short01Label,
    generatedAxisGlobalFifthRoot00Short02Label,
    generatedAxisGlobalFifthRoot00Short03Label,
    generatedAxisGlobalFifthRoot00Short04Label,
    generatedAxisGlobalFifthRoot00Short05Label,
    generatedAxisGlobalFifthRoot00Short06Label,
    generatedAxisGlobalFifthRoot00Short07Label,
    generatedAxisGlobalFifthRoot00Short08Label,
    generatedAxisGlobalFifthRoot00Short09Label,
    generatedAxisGlobalFifthRoot00Short10Label,
    generatedAxisGlobalFifthRoot00Short11Label,
    generatedAxisGlobalFifthRoot00Short12Label,
    generatedAxisGlobalFifthRoot00Short13Label,
    generatedAxisGlobalFifthRoot00Short14Label,
    generatedAxisGlobalFifthRoot00Short15Label,
    generatedAxisGlobalFifthRoot00Short16Label]

/-- All checked genuine central phases of the complete packet transport. -/
def generatedAxisGlobalFifthRoot00ShortPhases : Fin 17 → Fin 256 → ZMod 2 :=
  ![generatedAxisGlobalFifthRoot00Short00Phase,
    generatedAxisGlobalFifthRoot00Short01Phase,
    generatedAxisGlobalFifthRoot00Short02Phase,
    generatedAxisGlobalFifthRoot00Short03Phase,
    generatedAxisGlobalFifthRoot00Short04Phase,
    generatedAxisGlobalFifthRoot00Short05Phase,
    generatedAxisGlobalFifthRoot00Short06Phase,
    generatedAxisGlobalFifthRoot00Short07Phase,
    generatedAxisGlobalFifthRoot00Short08Phase,
    generatedAxisGlobalFifthRoot00Short09Phase,
    generatedAxisGlobalFifthRoot00Short10Phase,
    generatedAxisGlobalFifthRoot00Short11Phase,
    generatedAxisGlobalFifthRoot00Short12Phase,
    generatedAxisGlobalFifthRoot00Short13Phase,
    generatedAxisGlobalFifthRoot00Short14Phase,
    generatedAxisGlobalFifthRoot00Short15Phase,
    generatedAxisGlobalFifthRoot00Short16Phase]

/-- The assembled batch theorem retains both actual binary coordinates and central phases. -/
theorem generatedAxisGlobalFifthRoot00Short_batch_QImage (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketBatchNumber b i))) =
      qCentral (generatedAxisGlobalFifthRoot00ShortPhases b i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot00ShortLabels b i) := by
  fin_cases b
  · exact generatedAxisGlobalFifthRoot00Short00_QImage i
  · exact generatedAxisGlobalFifthRoot00Short01_QImage i
  · exact generatedAxisGlobalFifthRoot00Short02_QImage i
  · exact generatedAxisGlobalFifthRoot00Short03_QImage i
  · exact generatedAxisGlobalFifthRoot00Short04_QImage i
  · exact generatedAxisGlobalFifthRoot00Short05_QImage i
  · exact generatedAxisGlobalFifthRoot00Short06_QImage i
  · exact generatedAxisGlobalFifthRoot00Short07_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short08_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short09_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short10_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short11_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short12_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short13_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short14_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short15_encoded_QImage i
  · exact generatedAxisGlobalFifthRoot00Short16_encoded_QImage i

/-- The actual outgoing preferred-short coordinate of every original packet entry. -/
def generatedAxisGlobalFifthRoot00ShortLabel (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    GriessShortIndex :=
  generatedAxisGlobalFifthRoot00ShortLabels
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- The genuine central sign of every original packet entry. -/
def generatedAxisGlobalFifthRoot00ShortPhase (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    ZMod 2 :=
  generatedAxisGlobalFifthRoot00ShortPhases
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- Every original packet entry has its complete genuine preferred-Q image. -/
theorem generatedAxisGlobalFifthRoot00Short_QImage (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (generatedAxisGlobalFifthRoot00ShortPhase i) *
        griessShortQ (generatedAxisGlobalFifthRoot00ShortLabel i) := by
  have h := generatedAxisGlobalFifthRoot00Short_batch_QImage
    (⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩ : Fin 17)
    (⟨(generatedAxisGlobalFifthPacketNumber i).val % 256,
      Nat.mod_lt _ (by omega)⟩ : Fin 256)
  rw [generatedAxisGlobalFifthPacketBatchNumber_cover,
    generatedAxisGlobalFifthPacketFromNumber_number, generatedAxisGlobalShortQFinite_actual] at h
  exact h

/-- The entire actual real short constituent is the checked outgoing signed packet. -/
theorem generatedAxisGlobalFifthRoot00Short_actual :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 0)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot00ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot00ShortLabel i) (1 : ℝ) := by
  exact generatedAxisGlobalFifthPacketQFinite_transport 0 generatedAxisGlobalFifthQCache00_actual
    generatedAxisGlobalFifthRoot00ShortLabel generatedAxisGlobalFifthRoot00ShortPhase
    generatedAxisGlobalFifthRoot00Short_QImage

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
