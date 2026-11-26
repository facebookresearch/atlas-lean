/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm`

In the plane:
* `bc33_TavoidingRayData` is satisfiable: `bc35_TavoidingRayData_of_rootedArmDivergence` applied to
  the all-closed configuration (no trifurcations);
* `bc35_globalCutArm_of_singleCutTfree` and `bc35_downArmSplit_of_privateFar` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-closed configuration only a site is connected to itself. -/
theorem closed_connected_eq {a b : Site 2} (h : Connected 2 closed2 a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [closed2])

/-- Distinct sites have distinct clusters in the all-closed configuration. -/
theorem closed_cluster_ne {a b : Site 2} (hab : a ≠ b) :
    cluster 2 closed2 a ≠ cluster 2 closed2 b := by
  intro h
  have hb : b ∈ cluster 2 closed2 b := SimpleGraph.Reachable.refl b
  rw [← h] at hb
  exact hab (closed_connected_eq hb)

/-- The all-closed configuration has no trifurcation. -/
theorem closed_not_trif (x : Site 2) : ¬ IsTrifurcation 2 closed2 x := by
  rintro ⟨a₁, a₂, -, ⟨h12, -, -⟩, ⟨c1, c2, -⟩, -⟩
  exact h12 ((closed_connected_eq c1).symm.trans (closed_connected_eq c2))

-- Avoiding-ray data exist for the all-closed configuration.
example (n : ℕ) : ∃ rank : Site 2 → ℕ ×ₗ ℕ, bc33_TavoidingRayData closed2 n rank :=
  bc35_TavoidingRayData_of_rootedArmDivergence closed2 n
    (rfp_rootedArmDivergence_of_noTrif closed2 n fun x _ => closed_not_trif x)

-- A trifurcation-free single-cut arm is a global-cut arm.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (x bx : Site 2) (hb : bx ∈ box 2 n)
    (hc : Connected 2 ω x bx) (hinf : (cluster 2 (removeSite x ω) bx).Infinite)
    (hT : ∀ z, Connected 2 (removeSite x ω) bx z → z ∉ tfc_trifFinset ω n) :
    (cluster 2 (removeSites (tfc_trifFinset ω n) ω) bx).Infinite :=
  (bc35_globalCutArm_of_singleCutTfree ω n hb hc hinf hT).2.2

-- A private far arm splits from the down arm.
example (ω : ConfigSpace (Sym2 (Site 2))) (b : Site 2 → Site 2) (x y : Site 2)
    (h : bkfl_PrivateFar ω b y x) : ¬ Connected 2 (removeSite y ω) (b y) (b x) :=
  bc35_downArmSplit_of_privateFar ω b h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm
