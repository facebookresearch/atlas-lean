/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmForest`

* `bc51_globalArmForest_of_boundary_edge` in the configuration of `ℤ²` whose only open edge joins
  the boundary sites `(1, 0)` and `(1, 1)` of `B_1` (it has no trifurcation), so
  `bc51_GlobalArmForest` holds and `bc51_Tcount_le_boundary_of_globalArmForest` and
  `bc51_armForestReaching_of_globalArmForest` apply (non-vacuity).
* `Bc51Witness.catG_internal_lt_leaves`: the example tree has fewer branch vertices than leaves.
* A global arm forest cannot exist for every configuration of `ℤ` (refutation through
  `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The boundary site `(1, 0)` of `B_1 ⊂ ℤ²`. -/
def b₁ : Site 2 := ![1, 0]

/-- The boundary site `(1, 1)` of `B_1 ⊂ ℤ²`. -/
def b₂ : Site 2 := ![1, 1]

/-- The configuration of `ℤ²` whose only open edge is `{(1, 0), (1, 1)}`. -/
noncomputable def ωe : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = s(b₁, b₂))

/-- `(1, 0)` lies on the boundary of `B_1`. -/
theorem b₁_mem : b₁ ∈ vertexBoundary 2 1 :=
  ⟨fun i => by fin_cases i <;> simp [b₁], fun h => by simpa [b₁] using h 0⟩

/-- `(1, 1)` lies on the boundary of `B_1`. -/
theorem b₂_mem : b₂ ∈ vertexBoundary 2 1 :=
  ⟨fun i => by fin_cases i <;> simp [b₂], fun h => by simpa [b₂] using h 0⟩

/-- The two boundary sites are distinct. -/
theorem b₁_ne_b₂ : b₁ ≠ b₂ := fun h => by simpa [b₁, b₂] using congrFun h 1

/-- The edge `{(1, 0), (1, 1)}` is open in `ωe`. -/
theorem ωe_adj : (openSubgraph 2 ωe).Adj b₁ b₂ := by
  simp [ωe, b₁, b₂, Fin.sum_univ_two]

/-- In `ωe`, a site connected to `x` is `x`, `b₁` or `b₂`. -/
theorem ωe_connected {x y : Site 2} (h : Connected 2 ωe x y) : y = x ∨ y = b₁ ∨ y = b₂ := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Or.inl rfl
  | @cons u v z hadj _ ih =>
    have hv : (u = b₁ ∧ v = b₂) ∨ (u = b₂ ∧ v = b₁) := by
      have := hadj.2
      simpa [ωe] using this
    rcases ih with rfl | h | h
    · rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- No site is a trifurcation of `ωe`: every cluster has at most three sites. -/
theorem ωe_not_isTrifurcation (x : Site 2) : ¬ IsTrifurcation 2 ωe x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  refine h (((Set.finite_singleton a).insert b₁).insert b₂ |>.subset fun y hy => ?_)
  rcases ωe_connected hy with rfl | rfl | rfl <;> simp

/-- The global arm forest of the one-edge configuration. -/
theorem ωe_globalArmForest : bc51_GlobalArmForest ωe 1 :=
  bc51_globalArmForest_of_boundary_edge _ 1 b₁_mem b₂_mem b₁_ne_b₂ ωe_adj
    fun x _ => ωe_not_isTrifurcation x

-- The counting bound and arm-forest reaching for the one-edge configuration.
example : Tcount 2 ωe 1 ≤ boxSV_boundaryCard 2 1 ∧ sfa_ArmForestReaching ωe 1 :=
  ⟨bc51_Tcount_le_boundary_of_globalArmForest _ 1 ωe_globalArmForest,
    bc51_armForestReaching_of_globalArmForest _ 1 ωe_globalArmForest⟩

-- The caterpillar example has fewer branch vertices than leaves.
example : (Finset.univ.filter (fun v => 3 ≤ Bc51Witness.catG.degree v)).card
    < (Finset.univ.filter (fun v => Bc51Witness.catG.degree v = 1)).card :=
  Bc51Witness.catG_internal_lt_leaves

-- No configuration-wide global arm forest exists in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bc51_GlobalArmForest ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    bc51_Tcount_le_boundary_of_globalArmForest ω n (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmForest
