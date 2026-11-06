/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short13
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short14
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short15
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Short16

/-! Complete actual real short-coordinate transport of the fifth root-one normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All checked batch outputs, indexed by their exact finite packet numbers. -/
def generatedAxisGlobalFifthRoot01ShortLabels : Fin 17 → Fin 256 → GriessShortIndex :=
  generatedAxisGlobalFifthRoot01ShortLabelData

/-- All checked genuine central phases of the complete packet transport. -/
def generatedAxisGlobalFifthRoot01ShortPhases : Fin 17 → Fin 256 → ZMod 2 :=
  generatedAxisGlobalFifthRoot01ShortPhaseData

/-- The assembled batch theorem retains both actual binary coordinates and central phases. -/
theorem generatedAxisGlobalFifthRoot01Short_batch_QImage (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthQFast 1 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketBatchNumber b i))) =
      qCentral (generatedAxisGlobalFifthRoot01ShortPhases b i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot01ShortLabels b i) := by
  fin_cases b
  · exact generatedAxisGlobalFifthRoot01Short00_QImage i
  · exact generatedAxisGlobalFifthRoot01Short01_QImage i
  · exact generatedAxisGlobalFifthRoot01Short02_QImage i
  · exact generatedAxisGlobalFifthRoot01Short03_QImage i
  · exact generatedAxisGlobalFifthRoot01Short04_QImage i
  · exact generatedAxisGlobalFifthRoot01Short05_QImage i
  · exact generatedAxisGlobalFifthRoot01Short06_QImage i
  · exact generatedAxisGlobalFifthRoot01Short07_QImage i
  · exact generatedAxisGlobalFifthRoot01Short08_QImage i
  · exact generatedAxisGlobalFifthRoot01Short09_QImage i
  · exact generatedAxisGlobalFifthRoot01Short10_QImage i
  · exact generatedAxisGlobalFifthRoot01Short11_QImage i
  · exact generatedAxisGlobalFifthRoot01Short12_QImage i
  · exact generatedAxisGlobalFifthRoot01Short13_QImage i
  · exact generatedAxisGlobalFifthRoot01Short14_QImage i
  · exact generatedAxisGlobalFifthRoot01Short15_QImage i
  · exact generatedAxisGlobalFifthRoot01Short16_QImage i

/-- The actual outgoing preferred-short coordinate of every original packet entry. -/
def generatedAxisGlobalFifthRoot01ShortLabel (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    GriessShortIndex :=
  generatedAxisGlobalFifthRoot01ShortLabels
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- The genuine central sign of every original packet entry. -/
def generatedAxisGlobalFifthRoot01ShortPhase (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    ZMod 2 :=
  generatedAxisGlobalFifthRoot01ShortPhases
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- Every original packet entry has its complete genuine preferred-Q image. -/
theorem generatedAxisGlobalFifthRoot01Short_QImage (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthQFast 1 (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (generatedAxisGlobalFifthRoot01ShortPhase i) *
        griessShortQ (generatedAxisGlobalFifthRoot01ShortLabel i) := by
  have h := generatedAxisGlobalFifthRoot01Short_batch_QImage
    (⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩ : Fin 17)
    (⟨(generatedAxisGlobalFifthPacketNumber i).val % 256,
      Nat.mod_lt _ (by omega)⟩ : Fin 256)
  rw [generatedAxisGlobalFifthPacketBatchNumber_cover,
    generatedAxisGlobalFifthPacketFromNumber_number, generatedAxisGlobalShortQFinite_actual] at h
  exact h

/-- The entire actual real short constituent is the checked outgoing signed packet. -/
theorem generatedAxisGlobalFifthRoot01Short_actual :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 1)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot01ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot01ShortLabel i) (1 : ℝ) := by
  exact generatedAxisGlobalFifthPacketQFinite_transport 1 generatedAxisGlobalFifthQCache01_actual
    generatedAxisGlobalFifthRoot01ShortLabel generatedAxisGlobalFifthRoot01ShortPhase
    generatedAxisGlobalFifthRoot01Short_QImage

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
