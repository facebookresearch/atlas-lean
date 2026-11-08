/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint`

* `fkTheta` (the wired percolation probability) lies in `[0, 1]` on `ℤ²` at `p = 1/2`, `q = 2`;
* `fkSubcriticalSet d q` lies in `(0, 1)`, and it is empty for `q ≤ 0`, so `fkPc d 0 = 0`
  (the convention stated in the module doc);
* `mem_fkSubcriticalSet` unfolds membership.

Nonemptiness of `fkSubcriticalSet 2 q` for `q ≥ 1` and the bounds on `fkPc` are tested with
`PcNontrivial` and `CriticalPoint.DichotomyFull`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint

open _root_.StatMech _root_.StatMech.FK

-- `θ¹(1/2, 2)` on `ℤ²` is a probability.
example : 0 ≤ fkTheta 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) ∧
    fkTheta 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) ≤ 1 :=
  ⟨fkTheta_nonneg _ _ _ _, fkTheta_le_one _ _ _ _⟩

-- Every subcritical parameter lies in the open unit interval.
example (d : ℕ) (q : ℝ) : fkSubcriticalSet d q ⊆ Set.Ioo 0 1 :=
  fun _ ⟨hp, hp1, _, _⟩ => ⟨hp, hp1⟩

/-- For `q ≤ 0` the subcritical set is empty (no measure is defined). -/
theorem fkSubcriticalSet_eq_empty (d : ℕ) {q : ℝ} (hq : q ≤ 0) : fkSubcriticalSet d q = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, _, hq0, _⟩ => absurd hq0 (not_lt.mpr hq)

-- Hence the critical point is `sSup ∅ = 0` for `q = 0`.
example (d : ℕ) : fkPc d 0 = 0 := by
  rw [fkPc, fkSubcriticalSet_eq_empty d le_rfl, Real.sSup_empty]

-- Membership in the subcritical set unfolds to `θ¹(p, q) = 0`.
example (h : fkTheta 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) = 0) :
    (1 / 2 : ℝ) ∈ fkSubcriticalSet 2 2 :=
  mem_fkSubcriticalSet.mpr ⟨by norm_num, by norm_num, by norm_num, h⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
