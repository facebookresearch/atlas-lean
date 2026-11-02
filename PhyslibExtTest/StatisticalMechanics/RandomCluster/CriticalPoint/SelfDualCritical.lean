/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualCritical

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.DichotomyFull`

The hypotheses `hNoPercBelow` and `hPercAbove` of `beffaraDC_critical_point` are the
Beffara–Duminil-Copin theorem itself (2012); they are not proved in the library and are not
proved here. The tests check that the bookkeeping around them is not vacuous:
* the self-dual point is `p_sd(1) = 1/2` and `p_sd(q) ≥ 1/2` for `q ≥ 1`;
* `hNoPercBelow` holds unconditionally on the nonempty range `r < 1/4` (by the path-counting
  bound `θ¹(r, q) = 0` for `4 r < 1` on `ℤ²`), which lies below `p_sd(q)` for every `q ≥ 1`;
* the subcritical set `fkSubcriticalSet 2 q` is nonempty for `q = 1, 2`, so `fkPc 2 q` is a
  supremum of a nonempty bounded set and lies in `[1/8, 1]`;
* `mem_subcritical_of_lt_selfDualPoint`, `selfDualPoint_subcritical_le_fkPc`,
  `fkPc_le_selfDualPoint` and the headline are applied with the hypotheses as variables; at
  `q = 1` the headline gives `p_c = 1/2` (bond percolation).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.DichotomyFull

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.BeffaraDC

/-- The self-dual point of bond percolation is `1/2`. -/
theorem selfDualPoint_one : selfDualPoint 1 = 1 / 2 := by
  norm_num [selfDualPoint]

/-- For `q ≥ 1` the self-dual point is at least `1/2`. -/
theorem half_le_selfDualPoint {q : ℝ} (hq : 1 ≤ q) : 1 / 2 ≤ selfDualPoint q := by
  have hs : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  rw [selfDualPoint, le_div_iff₀ (by linarith)]
  linarith

/-- `hNoPercBelow` restricted to `r < 1/4` holds unconditionally: `θ¹(r, q) = 0` on `ℤ²`. -/
theorem noPerc_below_quarter {q : ℝ} (hq : 1 ≤ q) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r < 1 / 4) : fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0 :=
  fkTheta_eq_zero_of_lt (by norm_num) hr0 hr1 hq (by push_cast; linarith)

-- The unconditional range `r < 1/4` of `hNoPercBelow` is nonempty and lies below `p_sd(q)`.
example {q : ℝ} (hq : 1 ≤ q) : (1 / 8 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < selfDualPoint q :=
  ⟨by norm_num, by linarith [half_le_selfDualPoint hq]⟩

-- The subcritical set is nonempty at `q = 2` and `fkPc 2 2 ∈ [1/8, 1]`.
example : (fkSubcriticalSet 2 2).Nonempty ∧ 1 / 8 ≤ fkPc 2 2 ∧ fkPc 2 2 ≤ 1 := by
  have hmem : (1 / 8 : ℝ) ∈ fkSubcriticalSet 2 2 :=
    ⟨by norm_num, by norm_num, by norm_num,
      noPerc_below_quarter (q := 2) (by norm_num) _ (by norm_num) (by norm_num) (by norm_num)⟩
  exact ⟨⟨_, hmem⟩, le_fkPc_of_mem hmem,
    csSup_le ⟨_, hmem⟩ fun _ ⟨_, hp1, _, _⟩ => hp1.le⟩

-- The subcritical set is nonempty at `q = 1` (bond percolation).
example : (fkSubcriticalSet 2 1).Nonempty := fkSubcriticalSet_nonempty le_rfl

-- Under `hNoPercBelow`, every `p ∈ (0, p_sd(q))` is subcritical (here `p = 1/3`, `q = 2`).
example
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint 2 → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le (by norm_num : (1 : ℝ) ≤ 2))
        (q := 2) = 0) :
    (1 / 3 : ℝ) ∈ fkSubcriticalSet 2 2 :=
  mem_subcritical_of_lt_selfDualPoint (by norm_num) (by norm_num)
    (by linarith [half_le_selfDualPoint (q := 2) (by norm_num)]) hNoPercBelow

-- Under `hNoPercBelow` alone, `p_sd(q) ≤ p_c(q)`.
example {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
    selfDualPoint q ≤ fkPc 2 q :=
  selfDualPoint_subcritical_le_fkPc hq hNoPercBelow

-- Under `hPercAbove` alone, `p_c(q) ≤ p_sd(q)`.
example {q : ℝ} (hq : 1 ≤ q)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q ≤ selfDualPoint q :=
  fkPc_le_selfDualPoint hq hPercAbove

-- The headline at `q = 1`: the two hypotheses give Kesten's value `p_c = 1/2`.
example
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < Real.sqrt 1 / (1 + Real.sqrt 1) →
        fkTheta 2 hr0 hr1 (zero_lt_one.trans_le (le_refl (1 : ℝ))) (q := 1) = 0)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      Real.sqrt 1 / (1 + Real.sqrt 1) < r →
        0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le (le_refl (1 : ℝ))) (q := 1)) :
    fkPc 2 1 = 1 / 2 := by
  rw [beffaraDC_critical_point le_rfl hNoPercBelow hPercAbove]
  norm_num

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.DichotomyFull
