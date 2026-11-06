/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short13
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short14
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short15
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR09Short16

/-! Complete actual real short-coordinate transport of the fifth root-9 normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All checked batch outputs, indexed by their exact finite packet numbers. -/
def generatedAxisGlobalFifthRoot09ShortLabels : Fin 17 → Fin 256 → GriessShortIndex :=
  generatedAxisGlobalFifthRoot09ShortLabelData

/-- All checked genuine central phases of the complete packet transport. -/
def generatedAxisGlobalFifthRoot09ShortPhases : Fin 17 → Fin 256 → ZMod 2 :=
  generatedAxisGlobalFifthRoot09ShortPhaseData

/-- The assembled batch theorem retains both actual binary coordinates and central phases. -/
theorem generatedAxisGlobalFifthRoot09Short_batch_QImage (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthQFast 9 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketBatchNumber b i))) =
      qCentral (generatedAxisGlobalFifthRoot09ShortPhases b i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot09ShortLabels b i) := by
  fin_cases b
  · exact generatedAxisGlobalFifthRoot09Short00_QImage i
  · exact generatedAxisGlobalFifthRoot09Short01_QImage i
  · exact generatedAxisGlobalFifthRoot09Short02_QImage i
  · exact generatedAxisGlobalFifthRoot09Short03_QImage i
  · exact generatedAxisGlobalFifthRoot09Short04_QImage i
  · exact generatedAxisGlobalFifthRoot09Short05_QImage i
  · exact generatedAxisGlobalFifthRoot09Short06_QImage i
  · exact generatedAxisGlobalFifthRoot09Short07_QImage i
  · exact generatedAxisGlobalFifthRoot09Short08_QImage i
  · exact generatedAxisGlobalFifthRoot09Short09_QImage i
  · exact generatedAxisGlobalFifthRoot09Short10_QImage i
  · exact generatedAxisGlobalFifthRoot09Short11_QImage i
  · exact generatedAxisGlobalFifthRoot09Short12_QImage i
  · exact generatedAxisGlobalFifthRoot09Short13_QImage i
  · exact generatedAxisGlobalFifthRoot09Short14_QImage i
  · exact generatedAxisGlobalFifthRoot09Short15_QImage i
  · exact generatedAxisGlobalFifthRoot09Short16_QImage i

/-- The actual outgoing preferred-short coordinate of every original packet entry. -/
def generatedAxisGlobalFifthRoot09ShortLabel (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    GriessShortIndex :=
  generatedAxisGlobalFifthRoot09ShortLabels
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- The genuine central sign of every original packet entry. -/
def generatedAxisGlobalFifthRoot09ShortPhase (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    ZMod 2 :=
  generatedAxisGlobalFifthRoot09ShortPhases
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- Every original packet entry has its complete genuine preferred-Q image. -/
theorem generatedAxisGlobalFifthRoot09Short_QImage (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthQFast 9 (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (generatedAxisGlobalFifthRoot09ShortPhase i) *
        griessShortQ (generatedAxisGlobalFifthRoot09ShortLabel i) := by
  have h := generatedAxisGlobalFifthRoot09Short_batch_QImage
    (⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩ : Fin 17)
    (⟨(generatedAxisGlobalFifthPacketNumber i).val % 256,
      Nat.mod_lt _ (by omega)⟩ : Fin 256)
  rw [generatedAxisGlobalFifthPacketBatchNumber_cover,
    generatedAxisGlobalFifthPacketFromNumber_number, generatedAxisGlobalShortQFinite_actual] at h
  exact h

/-- The entire actual real short constituent is the checked outgoing signed packet. -/
theorem generatedAxisGlobalFifthRoot09Short_actual :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 9)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot09ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot09ShortLabel i) (1 : ℝ) := by
  exact generatedAxisGlobalFifthPacketQFinite_transport 9 generatedAxisGlobalFifthQCache09_actual
    generatedAxisGlobalFifthRoot09ShortLabel generatedAxisGlobalFifthRoot09ShortPhase
    generatedAxisGlobalFifthRoot09Short_QImage

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
