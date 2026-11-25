/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AccessibleSetsRecurrence
import Mathlib.Logic.Equiv.Bool
import Mathlib.Topology.Metrizable.Uniformity

/-! # Tests for partitions of sets of topological recurrence -/

namespace MetaMathlibExt.topological_recurrence_union_partition

-- At order zero, a single positive gap in the union suffices.
example (A B : Set ℕ) (hpos : A ∪ B ⊆ Set.Ioi 0) (hne : (A ∪ B).Nonempty) :
    IsLTopologicalRecurrence 0 A ∨ IsLTopologicalRecurrence 0 B := by
  apply topological_recurrence_union_partition 0 (A ∪ B) A B rfl
  obtain ⟨d, hd⟩ := hne
  refine ⟨hpos, fun X _ _ T _ U _ hU => ⟨d, hd, ?_⟩⟩
  simpa [iteratePreimage, Set.Nonempty] using hU

-- A two-point cycle rules out the gap one, so adjoining it cannot create order-one recurrence.
example (D : Set ℕ) (h : IsLTopologicalRecurrence 1 (D ∪ {1})) :
    IsLTopologicalRecurrence 1 D := by
  apply (topological_recurrence_union_partition 1 _ _ _ rfl h).resolve_right
  intro hone
  let : MetricSpace Bool := TopologicalSpace.metrizableSpaceMetric Bool
  let T := Equiv.boolNot.toHomeomorphOfDiscrete
  have hmin : IsMinimalSystem T := by
    rintro ⟨K, _, ⟨x, hx⟩, hproper, hinv⟩
    have hflip : (!x) ∈ K := by
      rw [← hinv]
      exact ⟨x, hx, rfl⟩
    apply hproper
    refine Set.eq_univ_of_forall fun y => ?_
    cases x <;> cases y <;> assumption
  obtain ⟨d, hd, x, hx⟩ :=
    hone.2 Bool T hmin {false} (isOpen_discrete _) (Set.singleton_nonempty _)
  obtain rfl : d = 1 := hd
  have hx₀ := Set.mem_iInter.mp hx (0 : Fin 2)
  have hx₁ := Set.mem_iInter.mp hx (1 : Fin 2)
  simp [iteratePreimage] at hx₀ hx₁
  subst x
  exact Bool.noConfusion hx₁

end MetaMathlibExt.topological_recurrence_union_partition
