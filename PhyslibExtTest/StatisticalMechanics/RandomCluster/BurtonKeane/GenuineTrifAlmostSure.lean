/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifAlmostSure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifAlmostSure`

* `bc89_upperLines_not_genuineTrif`: the upper-lines configuration has no classical trifurcation,
  and the classical count vanishes (`bc89_status`).
* `bc89_genuine_imp_isTrif` and the count comparison `bc89_genuineTcount ≤ Tcount` (`bc89_status`).
* `bc89_genuineTrif_open_degree_ge_three` on the complete graph on a three-site finset plus a
  centre (instance).
* `bc89_genuineTcount_le_boundary_of_openForest` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifAlmostSure

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The upper-lines configuration has no classical trifurcation, at the origin or in `B_5`.
example : ¬ bc89_GenuineTrif 2 bc60_upperLines 0 ∧ bc89_genuineTcount bc60_upperLines 5 = 0 :=
  ⟨bc89_upperLines_not_genuineTrif 0, bc89_status.2.2.2.1 5⟩

-- Classical trifurcations are weak trifurcations, so the classical count is the smaller one.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (h : bc89_GenuineTrif 2 ω x) :
    IsTrifurcation 2 ω x ∧ bc89_genuineTcount ω 3 ≤ Tcount 2 ω 3 :=
  ⟨bc89_genuine_imp_isTrif ω x h, bc89_status.2.1 ω 3⟩

/-- Four sites of `ℤ`: `0, 1, 2, 3`. -/
def V4 : Finset (Site 1) := {fun _ => 0, fun _ => 1, fun _ => 2, fun _ => 3}

/-- The site `fun _ => k` as an element of `V4`. -/
def v (k : ℤ) (hk : (fun _ => k : Site 1) ∈ V4) : (↑V4 : Type) := ⟨fun _ => k, hk⟩

-- In the complete graph on `V4`, the site `0` has three distinct neighbours, hence degree `≥ 3`.
example [DecidableRel (⊤ : SimpleGraph (↑V4 : Type)).Adj] :
    3 ≤ (⊤ : SimpleGraph (↑V4 : Type)).degree (v 0 (by simp [V4])) := by
  refine bc89_genuineTrif_open_degree_ge_three ⊤ (v 0 (by simp [V4]))
    ![v 1 (by simp [V4]), v 2 (by simp [V4]), v 3 (by simp [V4])] ?_ ?_
  · refine ⟨?_, ?_, ?_⟩ <;> simp [v, Subtype.ext_iff, funext_iff]
  · intro i; fin_cases i <;> simp [v, Subtype.ext_iff, funext_iff]

-- A box open forest bounds the classical count.
example (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n :=
  bc89_genuineTcount_le_boundary_of_openForest ω n h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifAlmostSure
