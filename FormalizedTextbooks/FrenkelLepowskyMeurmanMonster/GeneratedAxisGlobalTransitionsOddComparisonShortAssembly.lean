/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonMaskAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonShortData

/-! Complete actual comparison short constituents from three bounded preferred-Q batches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Every full local comparison uses exactly the stated original raw-coordinate representation. -/
theorem generatedAxisGlobalOddComparisonFiber_encode (k : Fin 3) (x : GriessSpace) :
    griessConwayEncode (rhoLocal (generatedAxisGlobalOddComparisonLocal k) x) =
      localConwayRawRepresentation (generatedAxisGlobalOddComparisonFiber k)
        (griessConwayEncode x) := by
  rw [← generatedAxisGlobalOddComparisonFiber_local]
  exact localGriessRepresentation_encode _ _

/-- Three complete preferred-Q batches cover the entire genuine comparison short constituent. -/
theorem generatedAxisGlobalOddComparisonShortBatches_transport (k : Fin 3)
    (hb : ∀ (b : Fin 3) (i : Fin 256),
      generatedAxisGlobalOddComparisonQImage k (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber b i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber b i)).2) =
      qCentral (generatedAxisGlobalOddComparisonShortPhases k
        (generatedAxisGlobalOddShortBatchNumber b i)) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddComparisonShortLabels k
          (generatedAxisGlobalOddShortBatchNumber b i))) :
    localShortOperator (generatedAxisGlobalOddComparisonFiber k)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddComparisonShortPhases k
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddComparisonShortLabels k
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddComparison_short_transport
  intro p
  let n := generatedAxisGlobalOddShortPacketNumber p
  have h := hb ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  simp only [generatedAxisGlobalOddShortBatchNumber_roundtrip] at h
  change generatedAxisGlobalOddComparisonQImage k (generatedAxisGlobalPairQFinite
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortPacketNumber p)).1
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortPacketNumber p)).2) = _ at h
  rw [generatedAxisGlobalOddShortPacketNumber_input,
    generatedAxisGlobalPairQFinite_actual, generatedAxisGlobalShortQFinite_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
