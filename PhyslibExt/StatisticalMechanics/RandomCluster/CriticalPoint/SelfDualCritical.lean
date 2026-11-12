/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PcLtOnePeierls
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue

/-!
# The critical point of the planar random-cluster model equals the self-dual point

If the wired planar random-cluster measure does not percolate below `p_sd(q) = √q / (1 + √q)` and
percolates above it, then `p_c(q) = p_sd(q)`.

## i. Overview

The Beffara–Duminil-Copin theorem states that for `q ≥ 1` the critical point of the
random-cluster model on `ℤ²` is the self-dual point `√q / (1 + √q)`. Its proof has two parts:
`θ(p, q) = 0` for `p < p_sd` (via sharp threshold and crossing estimates) and `θ(p, q) > 0` for
`p > p_sd` (via duality). This file proves only the last step: given both parts as hypotheses,
the supremum `fkPc 2 q` equals `p_sd(q)`. The hypotheses are not proved in this library.

## ii. Key results

- `selfDualPoint_subcritical_le_fkPc` : no percolation below `p_sd` gives `p_sd ≤ p_c`.
- `fkPc_le_selfDualPoint` : percolation above `p_sd` gives `p_c ≤ p_sd`.
- `beffaraDC_critical_point` : both hypotheses give `p_c(q) = √q / (1 + √q)`.

## iii. Table of contents

- A. Bounds on the critical point
- B. The critical point

## iv. References

- V. Beffara and H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
  model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

namespace StatMech

namespace BeffaraDC

open StatMech.FK

/-! ## A. Bounds on the critical point -/

lemma mem_subcritical_of_lt_selfDualPoint {q : ℝ} (hq : 1 ≤ q) {p : ℝ}
    (hp0 : 0 < p) (hp_sd : p < selfDualPoint q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
    p ∈ fkSubcriticalSet 2 q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hsd1 : selfDualPoint q < 1 := (selfDualPoint_mem_Ioo hq0).2
  have hp1 : p < 1 := hp_sd.trans hsd1
  refine ⟨hp0, hp1, hq0, ?_⟩
  exact hNoPercBelow p hp0 hp1 hp_sd

lemma selfDualPoint_subcritical_le_fkPc {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
    selfDualPoint q ≤ fkPc 2 q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine le_of_forall_lt_imp_le_of_dense (fun p hp => ?_)
  rcases le_or_gt p 0 with hp0 | hp0
  · exact hp0.trans (fkPc_pos (by norm_num) hq).le
  · have hmem : p ∈ fkSubcriticalSet 2 q :=
      mem_subcritical_of_lt_selfDualPoint hq hp0 hp hNoPercBelow
    exact le_csSup (fkSubcriticalSet_bddAbove 2 q) hmem

lemma fkPc_le_selfDualPoint {q : ℝ} (hq : 1 ≤ q)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q ≤ selfDualPoint q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine csSup_le (fkSubcriticalSet_nonempty hq) (fun r hr => ?_)
  obtain ⟨hr0, hr1, _hq0, hzero⟩ := hr
  by_contra hcon
  push Not at hcon
  have hθ : 0 < fkTheta 2 hr0 hr1 hq0 (q := q) := hPercAbove r hr0 hr1 hcon
  exact (not_mem_fkSubcriticalSet_of_fkTheta_pos hr0 hr1 hq0 hθ)
    ⟨hr0, hr1, hq0, hzero⟩

/-! ## B. The critical point -/

/-- If `θ(r, q) = 0` for `r < p_sd(q)` and `θ(r, q) > 0` for `r > p_sd(q)`, then
`p_c(q) = p_sd(q)`.
-/
lemma fkPc_eq_selfDualPoint {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q = selfDualPoint q :=
  le_antisymm (fkPc_le_selfDualPoint hq hPercAbove)
    (selfDualPoint_subcritical_le_fkPc hq hNoPercBelow)

/-- **Beffara–Duminil-Copin theorem, conditional form.** For `q ≥ 1`, if the wired random-cluster
measure on `ℤ²` does not percolate for `p < √q / (1 + √q)` (`hNoPercBelow`) and percolates for
`p > √q / (1 + √q)` (`hPercAbove`), then `p_c(q) = √q / (1 + √q)`.

The two hypotheses are the content of the Beffara–Duminil-Copin theorem and are not proved
here;
this statement only identifies the supremum defining `p_c(q)` once they hold. They are true for
every `q ≥ 1`, so the statement is not vacuous.
(V. Beffara and H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
model is critical for q ≥ 1*, Probab. Theory Related Fields 153, 2012.)
-/
theorem beffaraDC_critical_point {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < Real.sqrt q / (1 + Real.sqrt q) →
        fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      Real.sqrt q / (1 + Real.sqrt q) < r →
        0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q = Real.sqrt q / (1 + Real.sqrt q) := by
  have hval : selfDualPoint q = Real.sqrt q / (1 + Real.sqrt q) := rfl
  rw [← hval] at hNoPercBelow hPercAbove ⊢
  exact fkPc_eq_selfDualPoint hq hNoPercBelow hPercAbove

end BeffaraDC

end StatMech
