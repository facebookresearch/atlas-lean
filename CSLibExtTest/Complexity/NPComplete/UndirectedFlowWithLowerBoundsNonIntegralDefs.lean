/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegralDefs

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegral

open MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds
open MetaMathlibExt.BitstringEncoding

private theorem sum_three {M : Type} [AddCommMonoid M] (g : Fin 3 → M) :
    ∑ i, g i = g 0 + (g 1 + (g 2 + 0)) := rfl

private theorem sum_four {M : Type} [AddCommMonoid M] (g : Fin 4 → M) :
    ∑ i, g i = g 0 + (g 1 + (g 2 + (g 3 + 0))) := rfl

/-- Two routes `0 - 1 - 3` and `0 - 2 - 3` with capacity `1` and lower bound `0` on every
edge, from `0` to `3` with requirement `1`. -/
private abbrev diamond : UndirectedFlowWithLowerBoundsInstance :=
  (4, [(0, 1, 0, 1), (1, 3, 0, 1), (0, 2, 0, 1), (2, 3, 0, 1)], 0, 3, 1)

/-- The oriented edges that carry flow. -/
private abbrev used : List (ℕ × ℕ) := [(0, 1), (1, 3), (0, 2), (2, 3)]

/-- Half a unit along each of the two routes: a flow that is not integral. -/
private noncomputable def halfFlow (u v : Fin 4) : ℝ :=
  if ((u : ℕ), (v : ℕ)) ∈ used then 1 / 2 else 0

private theorem diamond_wellFormed : WellFormed diamond := by unfold WellFormed endpoints; decide

private theorem capacity_used :
    ∀ u v : Fin 4, ((u : ℕ), (v : ℕ)) ∈ used → capacity diamond u v = 1 := by decide

private theorem used_one_way :
    ∀ u v : Fin 4, ((u : ℕ), (v : ℕ)) ∈ used → ((v : ℕ), (u : ℕ)) ∉ used := by decide

private theorem lowerBound_zero : ∀ u v : Fin 4, lowerBound diamond u v = 0 := by decide

private theorem halfFlow_nonneg (u v : Fin 4) : 0 ≤ halfFlow u v := by
  unfold halfFlow; split <;> norm_num

/-- The instance is feasible with real flows, witnessed by `halfFlow`. -/
private theorem diamond_feasible : NonIntegralFeasible diamond := by
  refine ⟨by decide, by decide, halfFlow, ⟨halfFlow_nonneg, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    dsimp only
    unfold halfFlow
    split
    · rw [capacity_used u v ‹_›, Nat.cast_one, one_div]
      exact inv_le_one_of_one_le₀ one_le_two
    · exact Nat.cast_nonneg _
  · intro v h0 h3
    fin_cases v
    · exact absurd rfl h0
    · rw [sum_four, sum_four]; simp [halfFlow]
    · rw [sum_four, sum_four]; simp [halfFlow]
    · exact absurd rfl h3
  · intro u v _
    refine ⟨?_, ?_⟩
    · unfold halfFlow
      by_cases h : ((u : ℕ), (v : ℕ)) ∈ used
      · right; simp [used_one_way u v h]
      · left; simp [h]
    · rw [lowerBound_zero u v]
      exact le_max_of_le_left (by simpa using halfFlow_nonneg u v)
  · show ((1 : ℕ) : ℝ) ≤ (∑ u : Fin 4, halfFlow u 3) - ∑ w : Fin 4, halfFlow 3 w
    rw [sum_four, sum_four]
    simp [halfFlow]
    rw [← two_mul, mul_inv_cancel₀ two_ne_zero]

/-- From `0` to `1` with requirement `1`, through the edge `{0, 1}` (lower bound `0`, capacity
`1`), plus a dead end `{0, 2}` with lower bound `1` and capacity `1`. -/
private abbrev deadEnd : UndirectedFlowWithLowerBoundsInstance :=
  (3, [(0, 1, 0, 1), (0, 2, 1, 1)], 0, 1, 1)

example : WellFormed deadEnd := by unfold WellFormed endpoints; decide

/-- Real flows do not help the dead end: flow into `2` must return along the same edge, by
conservation, so using only one direction leaves `{0, 2}` below its lower bound. -/
private theorem deadEnd_infeasible : ¬ NonIntegralFeasible deadEnd := by
  rintro ⟨_, _, f, hfeas, hdir, -⟩
  obtain ⟨hnn, hcap, hcons⟩ := hfeas
  have hc : ∀ u v : Fin 3, f u v ≤ (capacity deadEnd u v : ℝ) := fun u v => hcap u v
  have k12 : capacity deadEnd ((1 : Fin 3) : ℕ) ((2 : Fin 3) : ℕ) = 0 := by decide
  have k21 : capacity deadEnd ((2 : Fin 3) : ℕ) ((1 : Fin 3) : ℕ) = 0 := by decide
  have l02 : lowerBound deadEnd ((0 : Fin 3) : ℕ) ((2 : Fin 3) : ℕ) = 1 := by decide
  have h12 := hc 1 2
  have h21 := hc 2 1
  rw [k12, Nat.cast_zero] at h12
  rw [k21, Nat.cast_zero] at h21
  have e12 : f 1 2 = 0 := le_antisymm h12 (hnn 1 2)
  have e21 : f 2 1 = 0 := le_antisymm h21 (hnn 2 1)
  have hc2 : ∑ u : Fin 3, f u 2 = ∑ w : Fin 3, f 2 w :=
    hcons 2 (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  rw [sum_three, sum_three, e12, e21] at hc2
  simp only [add_zero, zero_add, add_left_inj] at hc2
  obtain ⟨h | h, hl⟩ := hdir 0 2 (by simp [Graph, endpoints, Cslib.Complexity.Karp.edgeGraph])
  · rw [l02, h, ← hc2, h, max_self, Nat.cast_one] at hl
    exact absurd hl (not_le.mpr one_pos)
  · rw [l02, h, hc2, h, max_self, Nat.cast_one] at hl
    exact absurd hl (not_le.mpr one_pos)

/-- The decision problem accepts the encoding of `diamond`. -/
example : nonIntegralDec (bitEncode diamond) = true := by
  simp [nonIntegralDec, diamond_wellFormed, diamond_feasible]

/-- It rejects the encoding of the well-formed but infeasible `deadEnd`. -/
example : nonIntegralDec (bitEncode deadEnd) = false := by
  simp [nonIntegralDec, deadEnd_infeasible]

/-- It rejects an instance whose source `7` is not a vertex. -/
example : nonIntegralDec (bitEncode
    ((4, [(0, 1, 0, 1), (1, 3, 0, 1), (0, 2, 0, 1), (2, 3, 0, 1)], 7, 3, 1) :
      UndirectedFlowWithLowerBoundsInstance)) = false := by
  have h : ¬ NonIntegralFeasible
      ((4, [(0, 1, 0, 1), (1, 3, 0, 1), (0, 2, 0, 1), (2, 3, 0, 1)], 7, 3, 1) :
        UndirectedFlowWithLowerBoundsInstance) := fun ⟨hs, _⟩ => absurd hs (by decide)
  simp [nonIntegralDec, h]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : nonIntegralDec [true] = false := by
  have h : bitDecode (α := UndirectedFlowWithLowerBoundsInstance) [true] = none := rfl
  simp [nonIntegralDec, h]

end MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegral
