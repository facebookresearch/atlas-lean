/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQPacket07

/-! Every genuine source Q image and binary sign is retained in the complete short packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

private theorem packet_address (n : Fin 120) :
    ∃ k : Fin 8, ∃ q : Fin 15,
      generatedFeasibleContainingZeroOutsideAnchorPacketIndex k q = n := by
  let k : Fin 8 := ⟨n.val / 15, by omega⟩
  let q : Fin 15 := ⟨n.val % 15, Nat.mod_lt _ (by decide)⟩
  exact ⟨k, q, Fin.ext (by dsimp [generatedFeasibleContainingZeroOutsideAnchorPacketIndex, k, q]; omega)⟩

/-- Complete original preferred-Q images cover every source and target support address. -/
theorem generatedFeasibleContainingZeroOutsideAnchor_QImage (t : Fin 2) (n : Fin 120) :
    spinConjugation (generatedFeasibleContainingZeroOutsideAnchorStep t).val.1
      (griessShortQ (generatedFeasibleContainingZeroOutsideAnchorIndex
        (generatedFeasibleContainingZeroOutsideAnchorRoot (if t = 0 then 0 else 2) n))) =
      qCentral (generatedFeasibleContainingZeroOutsideAnchorPhase t n) *
        griessShortQ (generatedFeasibleContainingZeroOutsideAnchorIndex
          (generatedFeasibleContainingZeroOutsideAnchorRoot (if t = 0 then 1 else 3) n)) := by
  rw [generatedFeasibleContainingZeroOutsideAnchorQImage_actual,
    ← generatedFeasibleContainingZeroOutsideAnchorQ_actual,
    ← generatedFeasibleContainingZeroOutsideAnchorQ_actual]
  obtain ⟨k, q, hq⟩ := packet_address n
  rw [← hq]
  fin_cases k
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket00 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket01 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket02 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket03 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket04 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket05 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket06 t q
  · exact generatedFeasibleContainingZeroOutsideAnchorQPacket07 t q

/-- Every realized coefficient at every stage is a genuine unit sign. -/
theorem generatedFeasibleContainingZeroOutsideAnchorCoefficient_unit : ∀ k : Fin 4, ∀ n : Fin 120,
    generatedFeasibleContainingZeroOutsideAnchorCoefficient k n = 1 ∨
      generatedFeasibleContainingZeroOutsideAnchorCoefficient k n = -1 := by decide +kernel

/-- The complete actual central sign gives the recorded output unit coefficient. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPhase_coefficient (t : Fin 2) (n : Fin 120) :
    (generatedFeasibleContainingZeroOutsideAnchorCoefficient (if t = 0 then 0 else 2) n : ℝ) *
      qSign (generatedFeasibleContainingZeroOutsideAnchorPhase t n) =
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient (if t = 0 then 1 else 3) n : ℝ) := by
  have h : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      (a : ℝ) * qSign (if a = b then 0 else 1) = (b : ℝ) := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [qSign]
  exact h _ _ (generatedFeasibleContainingZeroOutsideAnchorCoefficient_unit _ _)
    (generatedFeasibleContainingZeroOutsideAnchorCoefficient_unit _ _)

/-- Every complete original short sum is transported by the actual source step. -/
theorem generatedFeasibleContainingZeroOutsideAnchorStep_short (t : Fin 2) :
    localShortOperator (generatedFeasibleContainingZeroOutsideAnchorStep t)
      (∑ n : Fin 120,
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient (if t = 0 then 0 else 2) n : ℝ) •
          Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex
            (generatedFeasibleContainingZeroOutsideAnchorRoot (if t = 0 then 0 else 2) n)) (1 : ℝ)) =
      ∑ n : Fin 120,
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient (if t = 0 then 1 else 3) n : ℝ) •
          Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex
            (generatedFeasibleContainingZeroOutsideAnchorRoot (if t = 0 then 1 else 3) n)) (1 : ℝ) := by
  rw [generatedFeasibleContainingZeroSparseShort_sum _ _ _ _ _
    (generatedFeasibleContainingZeroOutsideAnchor_QImage t)]
  simp_rw [generatedFeasibleContainingZeroOutsideAnchorPhase_coefficient]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
