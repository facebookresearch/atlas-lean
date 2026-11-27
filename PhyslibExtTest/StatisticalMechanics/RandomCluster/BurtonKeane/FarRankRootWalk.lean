/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FarRankRootWalk

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FarRankRootWalk`

* `bc44_chainFar_consistent`: the far-chain labelling on `Fin 3` is consistent;
* `bc44_farWitnessRank_distinct` at three explicit planar sites;
* `bc44_geometryConsistentRootWard_true` for the all-closed configuration;
* `bc44_rootWardRootParent_allRankPar_false_of_farParent` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FarRankRootWalk

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The far-chain labelling is consistent.
example : ∃ (x₀ y₀ z₀ : Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop),
    (∀ c u v, R c u v ↔ bc44_chainLab c u = bc44_chainLab c v) ∧
    x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ y₀ ≠ z₀ ∧ R 2 x₀ y₀ ∧ R 2 x₀ z₀ ∧ R 0 y₀ z₀ ∧ ¬ R 1 x₀ z₀ :=
  bc44_chainFar_consistent

/-- Three distinct planar sites. -/
theorem distinct3 : (0 : Site 2) ≠ ![1, 0] ∧ (0 : Site 2) ≠ ![0, 1] ∧
    (![1, 0] : Site 2) ≠ ![0, 1] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simpa using congrFun h 0
  · simpa using congrFun h 1
  · simpa using congrFun h 0

-- The far-witness rank separates the three sites.
example : bc44_farWitnessRank ![1, 0] ![0, 1] (0 : Site 2) ≠
    bc44_farWitnessRank ![1, 0] ![0, 1] ![1, 0] :=
  bc44_farWitnessRank_distinct distinct3.1 distinct3.2.1 distinct3.2.2 (Or.inl rfl)
    (Or.inr (Or.inl rfl)) distinct3.1

-- Geometry-consistent root-ward walks always exist.
example : bc44_GeometryConsistentRootWard closed2 3 (fun _ => toLex (0, 0)) id :=
  bc44_geometryConsistentRootWard_true closed2 3 _ _

-- A far parent refutes root-ward root parents.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (x₀ y₀ z₀ : Site 2)
    (hx : x₀ ∈ box 2 n) (tx : IsTrifurcation 2 ω x₀) (hy : y₀ ∈ box 2 n)
    (ty : IsTrifurcation 2 ω y₀) (hz : z₀ ∈ box 2 n) (tz : IsTrifurcation 2 ω z₀)
    (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀)
    (hex : ∀ a, a ∈ box 2 n → IsTrifurcation 2 ω a → a = x₀ ∨ a = y₀ ∨ a = z₀)
    (hconn : Connected 2 ω x₀ y₀) (hadj : bc37_ArmAdjacent ω n y₀ z₀)
    (hfar : ¬ Connected 2 (removeSite y₀ ω) x₀ z₀) :
    ¬ ∀ (rank : Site 2 → ℕ ×ₗ ℕ) (par : Site 2 → Site 2), bc43_RootWardRootParent ω n rank par :=
  bc44_rootWardRootParent_allRankPar_false_of_farParent ω n hx tx hy ty hz tz hxy hxz hyz hex
    hconn hadj hfar

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FarRankRootWalk
