/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short13
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short14
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short15
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Short16

/-! Complete actual real short-coordinate transport of the fifth root-4 normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All checked batch outputs, indexed by their exact finite packet numbers. -/
def generatedAxisGlobalFifthRoot04ShortLabels : Fin 17 → Fin 256 → GriessShortIndex :=
  generatedAxisGlobalFifthRoot04ShortLabelData

/-- All checked genuine central phases of the complete packet transport. -/
def generatedAxisGlobalFifthRoot04ShortPhases : Fin 17 → Fin 256 → ZMod 2 :=
  generatedAxisGlobalFifthRoot04ShortPhaseData

/-- The assembled batch theorem retains both actual binary coordinates and central phases. -/
theorem generatedAxisGlobalFifthRoot04Short_batch_QImage (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthQFast 4 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketBatchNumber b i))) =
      qCentral (generatedAxisGlobalFifthRoot04ShortPhases b i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot04ShortLabels b i) := by
  fin_cases b
  · exact generatedAxisGlobalFifthRoot04Short00_QImage i
  · exact generatedAxisGlobalFifthRoot04Short01_QImage i
  · exact generatedAxisGlobalFifthRoot04Short02_QImage i
  · exact generatedAxisGlobalFifthRoot04Short03_QImage i
  · exact generatedAxisGlobalFifthRoot04Short04_QImage i
  · exact generatedAxisGlobalFifthRoot04Short05_QImage i
  · exact generatedAxisGlobalFifthRoot04Short06_QImage i
  · exact generatedAxisGlobalFifthRoot04Short07_QImage i
  · exact generatedAxisGlobalFifthRoot04Short08_QImage i
  · exact generatedAxisGlobalFifthRoot04Short09_QImage i
  · exact generatedAxisGlobalFifthRoot04Short10_QImage i
  · exact generatedAxisGlobalFifthRoot04Short11_QImage i
  · exact generatedAxisGlobalFifthRoot04Short12_QImage i
  · exact generatedAxisGlobalFifthRoot04Short13_QImage i
  · exact generatedAxisGlobalFifthRoot04Short14_QImage i
  · exact generatedAxisGlobalFifthRoot04Short15_QImage i
  · exact generatedAxisGlobalFifthRoot04Short16_QImage i

/-- The actual outgoing preferred-short coordinate of every original packet entry. -/
def generatedAxisGlobalFifthRoot04ShortLabel (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    GriessShortIndex :=
  generatedAxisGlobalFifthRoot04ShortLabels
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- The genuine central sign of every original packet entry. -/
def generatedAxisGlobalFifthRoot04ShortPhase (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    ZMod 2 :=
  generatedAxisGlobalFifthRoot04ShortPhases
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- Every original packet entry has its complete genuine preferred-Q image. -/
theorem generatedAxisGlobalFifthRoot04Short_QImage (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthQFast 4 (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (generatedAxisGlobalFifthRoot04ShortPhase i) *
        griessShortQ (generatedAxisGlobalFifthRoot04ShortLabel i) := by
  have h := generatedAxisGlobalFifthRoot04Short_batch_QImage
    (⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩ : Fin 17)
    (⟨(generatedAxisGlobalFifthPacketNumber i).val % 256,
      Nat.mod_lt _ (by omega)⟩ : Fin 256)
  rw [generatedAxisGlobalFifthPacketBatchNumber_cover,
    generatedAxisGlobalFifthPacketFromNumber_number, generatedAxisGlobalShortQFinite_actual] at h
  exact h

/-- The entire actual real short constituent is the checked outgoing signed packet. -/
theorem generatedAxisGlobalFifthRoot04Short_actual :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 4)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot04ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot04ShortLabel i) (1 : ℝ) := by
  exact generatedAxisGlobalFifthPacketQFinite_transport 4 generatedAxisGlobalFifthQCache04_actual
    generatedAxisGlobalFifthRoot04ShortLabel generatedAxisGlobalFifthRoot04ShortPhase
    generatedAxisGlobalFifthRoot04Short_QImage

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
