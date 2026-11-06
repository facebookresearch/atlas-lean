/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short13
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short14
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short15
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR08Short16

/-! Complete actual real short-coordinate transport of the fifth root-8 normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All checked batch outputs, indexed by their exact finite packet numbers. -/
def generatedAxisGlobalFifthRoot08ShortLabels : Fin 17 → Fin 256 → GriessShortIndex :=
  generatedAxisGlobalFifthRoot08ShortLabelData

/-- All checked genuine central phases of the complete packet transport. -/
def generatedAxisGlobalFifthRoot08ShortPhases : Fin 17 → Fin 256 → ZMod 2 :=
  generatedAxisGlobalFifthRoot08ShortPhaseData

/-- The assembled batch theorem retains both actual binary coordinates and central phases. -/
theorem generatedAxisGlobalFifthRoot08Short_batch_QImage (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthQFast 8 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketBatchNumber b i))) =
      qCentral (generatedAxisGlobalFifthRoot08ShortPhases b i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot08ShortLabels b i) := by
  fin_cases b
  · exact generatedAxisGlobalFifthRoot08Short00_QImage i
  · exact generatedAxisGlobalFifthRoot08Short01_QImage i
  · exact generatedAxisGlobalFifthRoot08Short02_QImage i
  · exact generatedAxisGlobalFifthRoot08Short03_QImage i
  · exact generatedAxisGlobalFifthRoot08Short04_QImage i
  · exact generatedAxisGlobalFifthRoot08Short05_QImage i
  · exact generatedAxisGlobalFifthRoot08Short06_QImage i
  · exact generatedAxisGlobalFifthRoot08Short07_QImage i
  · exact generatedAxisGlobalFifthRoot08Short08_QImage i
  · exact generatedAxisGlobalFifthRoot08Short09_QImage i
  · exact generatedAxisGlobalFifthRoot08Short10_QImage i
  · exact generatedAxisGlobalFifthRoot08Short11_QImage i
  · exact generatedAxisGlobalFifthRoot08Short12_QImage i
  · exact generatedAxisGlobalFifthRoot08Short13_QImage i
  · exact generatedAxisGlobalFifthRoot08Short14_QImage i
  · exact generatedAxisGlobalFifthRoot08Short15_QImage i
  · exact generatedAxisGlobalFifthRoot08Short16_QImage i

/-- The actual outgoing preferred-short coordinate of every original packet entry. -/
def generatedAxisGlobalFifthRoot08ShortLabel (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    GriessShortIndex :=
  generatedAxisGlobalFifthRoot08ShortLabels
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- The genuine central sign of every original packet entry. -/
def generatedAxisGlobalFifthRoot08ShortPhase (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    ZMod 2 :=
  generatedAxisGlobalFifthRoot08ShortPhases
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- Every original packet entry has its complete genuine preferred-Q image. -/
theorem generatedAxisGlobalFifthRoot08Short_QImage (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthQFast 8 (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (generatedAxisGlobalFifthRoot08ShortPhase i) *
        griessShortQ (generatedAxisGlobalFifthRoot08ShortLabel i) := by
  have h := generatedAxisGlobalFifthRoot08Short_batch_QImage
    (⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩ : Fin 17)
    (⟨(generatedAxisGlobalFifthPacketNumber i).val % 256,
      Nat.mod_lt _ (by omega)⟩ : Fin 256)
  rw [generatedAxisGlobalFifthPacketBatchNumber_cover,
    generatedAxisGlobalFifthPacketFromNumber_number, generatedAxisGlobalShortQFinite_actual] at h
  exact h

/-- The entire actual real short constituent is the checked outgoing signed packet. -/
theorem generatedAxisGlobalFifthRoot08Short_actual :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 8)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot08ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot08ShortLabel i) (1 : ℝ) := by
  exact generatedAxisGlobalFifthPacketQFinite_transport 8 generatedAxisGlobalFifthQCache08_actual
    generatedAxisGlobalFifthRoot08ShortLabel generatedAxisGlobalFifthRoot08ShortPhase
    generatedAxisGlobalFifthRoot08Short_QImage

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
