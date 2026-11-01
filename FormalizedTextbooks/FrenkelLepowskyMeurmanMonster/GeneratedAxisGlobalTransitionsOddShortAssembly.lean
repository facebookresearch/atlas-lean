/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMaskEncode

/-! Assembly of all 552 genuine preferred-short images from three bounded finite batches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

/-- Number of an original preferred pair coordinate in the complete 552-entry packet. -/
def generatedAxisGlobalOddShortPacketNumber (p : GeneratedAxisGlobalOddShortPacketIndex) :
    Fin 552 := ⟨276 * p.1.val + p.2.val, by omega⟩

/-- Numbering retains both original pair coordinates. -/
theorem generatedAxisGlobalOddShortPacketNumber_input
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortPacketNumber p) = p := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [generatedAxisGlobalOddShortInput, generatedAxisGlobalOddShortPacketNumber] <;>
    omega

/-- Each original packet entry occurs in the indicated one of three 256-entry batches. -/
theorem generatedAxisGlobalOddShortBatchNumber_roundtrip (n : Fin 552) :
    generatedAxisGlobalOddShortBatchNumber
      ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩ = n := by
  apply Fin.ext
  simp only [generatedAxisGlobalOddShortBatchNumber]
  omega

/-- The three complete batch certificates cover every actual packet entry. -/
theorem generatedAxisGlobalOddShortBatches_cover (k : Fin 9)
    (hb : ∀ (b : Fin 3) (i : Fin 256),
      generatedAxisGlobalOddRootQFast k (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber b i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber b i)).2) =
      qCentral (generatedAxisGlobalOddShortRootPhases k
        (generatedAxisGlobalOddShortBatchNumber b i)) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddShortRootLabels k
          (generatedAxisGlobalOddShortBatchNumber b i))) (n : Fin 552) :
    generatedAxisGlobalOddRootQFast k (generatedAxisGlobalPairQFinite
      (generatedAxisGlobalOddShortInput n).1 (generatedAxisGlobalOddShortInput n).2) =
      qCentral (generatedAxisGlobalOddShortRootPhases k n) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddShortRootLabels k n) := by
  have h := hb ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [generatedAxisGlobalOddShortBatchNumber_roundtrip] using h

/-- Complete source coordinate and batch certificates give the entire actual short constituent. -/
theorem generatedAxisGlobalOddShortBatches_transport (k : Fin 9)
    (hk : ∀ i, generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k)
      (qCoordinateGenerator i) = generatedAxisGlobalOddRootQCache k i)
    (hb : ∀ (b : Fin 3) (i : Fin 256),
      generatedAxisGlobalOddRootQFast k (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber b i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber b i)).2) =
      qCentral (generatedAxisGlobalOddShortRootPhases k
        (generatedAxisGlobalOddShortBatchNumber b i)) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddShortRootLabels k
          (generatedAxisGlobalOddShortBatchNumber b i))) :
    localShortOperator (generatedAxisGlobalOddSourceRootFiber k)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases k
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels k
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddShortPacket_transport
  intro p
  have h := generatedAxisGlobalOddShortBatches_cover k hb
    (generatedAxisGlobalOddShortPacketNumber p)
  rw [generatedAxisGlobalOddShortPacketNumber_input] at h
  rw [generatedAxisGlobalPairQFinite_actual, generatedAxisGlobalShortQFinite_actual] at h
  rw [← generatedAxisGlobalOddRootQFast_actual k hk,
    ← generatedAxisGlobalOddSourceFastRoot_actual,
    generatedAxisGlobalOddSourceRoot_QImage] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
