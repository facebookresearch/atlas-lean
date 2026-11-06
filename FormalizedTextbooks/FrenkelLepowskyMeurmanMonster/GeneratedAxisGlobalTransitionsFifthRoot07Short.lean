/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short01
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short02
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short03
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short04
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short05
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short06
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short07
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short09
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short10
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short12
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short13
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short14
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short15
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR07Short16

/-! Complete actual real short-coordinate transport of the fifth root-7 normalization word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All checked batch outputs, indexed by their exact finite packet numbers. -/
def generatedAxisGlobalFifthRoot07ShortLabels : Fin 17 → Fin 256 → GriessShortIndex :=
  generatedAxisGlobalFifthRoot07ShortLabelData

/-- All checked genuine central phases of the complete packet transport. -/
def generatedAxisGlobalFifthRoot07ShortPhases : Fin 17 → Fin 256 → ZMod 2 :=
  generatedAxisGlobalFifthRoot07ShortPhaseData

/-- The assembled batch theorem retains both actual binary coordinates and central phases. -/
theorem generatedAxisGlobalFifthRoot07Short_batch_QImage (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthQFast 7 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketBatchNumber b i))) =
      qCentral (generatedAxisGlobalFifthRoot07ShortPhases b i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot07ShortLabels b i) := by
  fin_cases b
  · exact generatedAxisGlobalFifthRoot07Short00_QImage i
  · exact generatedAxisGlobalFifthRoot07Short01_QImage i
  · exact generatedAxisGlobalFifthRoot07Short02_QImage i
  · exact generatedAxisGlobalFifthRoot07Short03_QImage i
  · exact generatedAxisGlobalFifthRoot07Short04_QImage i
  · exact generatedAxisGlobalFifthRoot07Short05_QImage i
  · exact generatedAxisGlobalFifthRoot07Short06_QImage i
  · exact generatedAxisGlobalFifthRoot07Short07_QImage i
  · exact generatedAxisGlobalFifthRoot07Short08_QImage i
  · exact generatedAxisGlobalFifthRoot07Short09_QImage i
  · exact generatedAxisGlobalFifthRoot07Short10_QImage i
  · exact generatedAxisGlobalFifthRoot07Short11_QImage i
  · exact generatedAxisGlobalFifthRoot07Short12_QImage i
  · exact generatedAxisGlobalFifthRoot07Short13_QImage i
  · exact generatedAxisGlobalFifthRoot07Short14_QImage i
  · exact generatedAxisGlobalFifthRoot07Short15_QImage i
  · exact generatedAxisGlobalFifthRoot07Short16_QImage i

/-- The actual outgoing preferred-short coordinate of every original packet entry. -/
def generatedAxisGlobalFifthRoot07ShortLabel (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    GriessShortIndex :=
  generatedAxisGlobalFifthRoot07ShortLabels
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- The genuine central sign of every original packet entry. -/
def generatedAxisGlobalFifthRoot07ShortPhase (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    ZMod 2 :=
  generatedAxisGlobalFifthRoot07ShortPhases
    ⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩
    ⟨(generatedAxisGlobalFifthPacketNumber i).val % 256, Nat.mod_lt _ (by omega)⟩

/-- Every original packet entry has its complete genuine preferred-Q image. -/
theorem generatedAxisGlobalFifthRoot07Short_QImage (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthQFast 7 (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (generatedAxisGlobalFifthRoot07ShortPhase i) *
        griessShortQ (generatedAxisGlobalFifthRoot07ShortLabel i) := by
  have h := generatedAxisGlobalFifthRoot07Short_batch_QImage
    (⟨(generatedAxisGlobalFifthPacketNumber i).val / 256, by omega⟩ : Fin 17)
    (⟨(generatedAxisGlobalFifthPacketNumber i).val % 256,
      Nat.mod_lt _ (by omega)⟩ : Fin 256)
  rw [generatedAxisGlobalFifthPacketBatchNumber_cover,
    generatedAxisGlobalFifthPacketFromNumber_number, generatedAxisGlobalShortQFinite_actual] at h
  exact h

/-- The entire actual real short constituent is the checked outgoing signed packet. -/
theorem generatedAxisGlobalFifthRoot07Short_actual :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 7)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot07ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot07ShortLabel i) (1 : ℝ) := by
  exact generatedAxisGlobalFifthPacketQFinite_transport 7 generatedAxisGlobalFifthQCache07_actual
    generatedAxisGlobalFifthRoot07ShortLabel generatedAxisGlobalFifthRoot07ShortPhase
    generatedAxisGlobalFifthRoot07Short_QImage

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
