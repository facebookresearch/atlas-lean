/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusDefectClassify
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue

/-!
# Comparing the torus partition functions under duality

Partition functions and numerators on the triangular and hexagonal tori, their exact duality
with the topological weight `q ^ defect`, and two-sided bounds removing that weight.

## i. Overview

Summing the FK-weight duality of `TriHex.TorusDuality` over configurations expresses the
triangular partition function at `(p, q)` through a defect-weighted hexagonal partition function
at `(p*, q)` (`triHexTorus_partition_duality_defectWeighted`), and the same for numerators of
expectations of functions of the dual configuration. Since the defect lies in `{0, 1, 2}`, for
`q ≥ 1` the weight `q ^ defect` is between `1` and `q²`; hence the defect-weighted sums are
within a factor `q²` of the plain dual sums, and the correction to the free energy per site
vanishes as `L → ∞`. All results are proved unconditionally under the stated parameter
ranges.

## ii. Key results

- `triHexTorus_partition_duality_defectWeighted`, `triHexTorus_numerator_duality_defectWeighted`.
- `triHexTorus_defectWeighted_partition_bounds`, `triHexTorus_defectWeighted_normalized_bounds`.
- `triHexTorus_topologicalCorrection_logDensity_tendsto_zero`.

## iii. Table of contents

- A. Partition functions and numerators
- B. Bounds on the topological weight
- C. Sector decompositions
- D. Duality of partition functions and numerators
- E. Removing the topological weight

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 6.
- V. Beffara and H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
  model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), 511–542.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

/-! ## A. Partition functions and numerators -/

/-- The FK partition function of the triangular torus at `(p, q)`. -/
noncomputable def triHexTorusPrimalPartitionSum
    (L : ℕ) [Fact (2 < L)] (p q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    FK.fkWeight (triangularTorusGraph L) p q omega

/-- The FK partition function of the hexagonal torus at `(pDual, q)`, written as a sum over
triangular configurations through the dual map. -/
noncomputable def triHexTorusDualPartitionSum
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    FK.fkWeight (hexagonalTorusGraph L) pDual q
      (triHexTorusDualConfig L omega)

/-- The hexagonal partition function with each term weighted by `q ^ defect` of the primal
configuration. -/
noncomputable def triHexTorusDefectWeightedDualPartitionSum
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    FK.fkWeight (hexagonalTorusGraph L) pDual q
        (triHexTorusDualConfig L omega) *
      q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega)

/-- Unnormalized triangular expectation of `F` of the dual configuration. -/
noncomputable def triHexTorusPrimalNumerator
    (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    F (triHexTorusDualConfig L omega) *
      FK.fkWeight (triangularTorusGraph L) p q omega

/-- Unnormalized hexagonal expectation of `F`. -/
noncomputable def triHexTorusDualNumerator
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    F (triHexTorusDualConfig L omega) *
      FK.fkWeight (hexagonalTorusGraph L) pDual q
        (triHexTorusDualConfig L omega)

/-- Unnormalized hexagonal expectation of `F`, weighted by `q ^ defect`. -/
noncomputable def triHexTorusDefectWeightedDualNumerator
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    F (triHexTorusDualConfig L omega) *
      FK.fkWeight (hexagonalTorusGraph L) pDual q
        (triHexTorusDualConfig L omega) *
      q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega)

/-! ## B. Bounds on the topological weight -/

lemma triHexTorus_topologicalCorrection_bounds
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L)))
    {q : ℝ} (hq : 1 ≤ q) :
    1 ≤ q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega) ∧
      q ^ triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) ≤ q ^ 2 := by
  rcases triHexTorusDefect_openSub_classified L omega with h | h | h
  · rw [h]
    rw [zpow_zero]
    exact ⟨le_rfl, one_le_pow₀ hq⟩
  · rw [h]
    rw [zpow_one]
    refine ⟨hq, ?_⟩
    have hq0 : 0 ≤ q := zero_le_one.trans hq
    simpa [pow_two] using mul_le_mul_of_nonneg_right hq hq0
  · rw [h]
    rw [zpow_ofNat]
    exact ⟨one_le_pow₀ hq, le_rfl⟩

lemma triHexTorus_topologicalCorrection_log_bound
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L)))
    {q : ℝ} (hq : 1 ≤ q) :
    |Real.log (q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega))| ≤
      2 * Real.log q := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
  rcases triHexTorusDefect_openSub_classified L omega with h | h | h
  · rw [h]
    rw [zpow_zero, Real.log_one, abs_zero]
    exact mul_nonneg (by norm_num) hlog
  · rw [h]
    rw [zpow_one, abs_of_nonneg hlog]
    linarith
  · rw [h]
    rw [zpow_ofNat, Real.log_pow]
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hlog)]
    norm_num

/-- `|log q ^ defect| / L²` on the torus of side `L = n + 3`, for a chosen configuration on each
torus. -/
noncomputable def triHexTorusTopologicalCorrectionLogDensity
    (q : ℝ)
    (omega : ∀ L : ℕ, ConfigSpace (Sym2 (TorusSite L)))
    (n : ℕ) : ℝ := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by simp [L]⟩
  exact |Real.log (q ^ triHexTorusDefect L
    (FK.openSub (triangularTorusGraph L) (omega L)))| / (L ^ 2 : ℕ)

/-- The topological correction per site vanishes in the thermodynamic limit. -/
lemma triHexTorus_topologicalCorrection_logDensity_tendsto_zero
    (q : ℝ) (hq : 1 ≤ q)
    (omega : ∀ L : ℕ, ConfigSpace (Sym2 (TorusSite L))) :
    Filter.Tendsto
      (triHexTorusTopologicalCorrectionLogDensity q omega)
      Filter.atTop (nhds 0) := by
  let C : ℝ := 2 * Real.log q
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.log_nonneg hq)
  have hub : ∀ n : ℕ,
      triHexTorusTopologicalCorrectionLogDensity q omega n ≤
        C / ((n + 1 : ℕ) : ℝ) := by
    intro n
    let L := n + 3
    let : Fact (2 < L) := ⟨by simp [L]⟩
    have hlog := triHexTorus_topologicalCorrection_log_bound
      L (omega L) hq
    have hden0 : 0 ≤ ((L ^ 2 : ℕ) : ℝ) := by positivity
    have hsmall0 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hden : ((n + 1 : ℕ) : ℝ) ≤ ((L ^ 2 : ℕ) : ℝ) := by
      norm_num [L]
      exact_mod_cast (show n + 1 ≤ (n + 3) ^ 2 by nlinarith)
    unfold triHexTorusTopologicalCorrectionLogDensity
    dsimp only
    calc
      |Real.log (q ^ triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) (omega L)))| /
            ((L ^ 2 : ℕ) : ℝ) ≤ C / ((L ^ 2 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hlog hden0
      _ ≤ C / ((n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hC hsmall0 hden
  have hupper : Filter.Tendsto
      (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (Filter.tendsto_add_atTop_nat 1)
  apply squeeze_zero
  · intro n
    unfold triHexTorusTopologicalCorrectionLogDensity
    positivity
  · exact hub
  · exact hupper

/-! ## C. Sector decompositions -/

lemma triHexTorusDualPartitionSum_eq_sectorSum
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ) :
    triHexTorusDualPartitionSum L pDual q =
      triHexTorusDualSectorSum L 0 pDual q (fun _ => 1) +
        triHexTorusDualSectorSum L 1 pDual q (fun _ => 1) +
          triHexTorusDualSectorSum L 2 pDual q (fun _ => 1) := by
  classical
  unfold triHexTorusDualPartitionSum triHexTorusDualSectorSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro omega homega
  rcases triHexTorusDefect_openSub_classified L omega with h | h | h <;>
    simp [h]

lemma triHexTorusDefectWeightedDualPartitionSum_eq_sectorSum
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ) :
    triHexTorusDefectWeightedDualPartitionSum L pDual q =
      triHexTorusDualSectorSum L 0 pDual q (fun _ => 1) +
        q * triHexTorusDualSectorSum L 1 pDual q (fun _ => 1) +
          q ^ 2 * triHexTorusDualSectorSum L 2 pDual q (fun _ => 1) := by
  classical
  unfold triHexTorusDefectWeightedDualPartitionSum
  unfold triHexTorusDualSectorSum
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro omega homega
  rcases triHexTorusDefect_openSub_classified L omega with h | h | h
  · simp [h]
  · simp [h]
    ring
  · simp [h, zpow_ofNat]
    ring

/-! ## D. Duality of partition functions and numerators -/

/-- Duality of torus partition functions: triangular at `(p, q)` against defect-weighted hexagonal
at `(p*, q)`. -/
theorem triHexTorus_partition_duality_defectWeighted
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexTorusPrimalPartitionSum L p q *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q := by
  classical
  unfold triHexTorusPrimalPartitionSum
  unfold triHexTorusDefectWeightedDualPartitionSum
  rw [Finset.sum_mul]
  calc
    ∑ omega, FK.fkWeight (triangularTorusGraph L) p q omega *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      ∑ omega,
        (p / (1 - BeffaraDC.dualParam p q)) ^
            (triangularTorusGraph L).edgeFinset.card *
          q ^ Nat.card (TorusSite L) *
          (FK.fkWeight (hexagonalTorusGraph L)
              (BeffaraDC.dualParam p q) q
              (triHexTorusDualConfig L omega) *
            q ^ triHexTorusDefect L
              (FK.openSub (triangularTorusGraph L) omega)) := by
        apply Finset.sum_congr rfl
        intro omega homega
        have h := triHexTorus_fkWeight_duality_signed L omega hp hp1 hq
        linarith
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        (∑ omega,
          FK.fkWeight (hexagonalTorusGraph L)
              (BeffaraDC.dualParam p q) q
              (triHexTorusDualConfig L omega) *
          q ^ triHexTorusDefect L
              (FK.openSub (triangularTorusGraph L) omega)) := by
      rw [Finset.mul_sum]

/-- Duality of torus expectation numerators. -/
lemma triHexTorus_numerator_duality_defectWeighted
    (L : ℕ) [Fact (2 < L)]
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexTorusPrimalNumerator L p q F *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        triHexTorusDefectWeightedDualNumerator L
          (BeffaraDC.dualParam p q) q F := by
  classical
  unfold triHexTorusPrimalNumerator
  unfold triHexTorusDefectWeightedDualNumerator
  rw [Finset.sum_mul]
  calc
    ∑ omega,
        (F (triHexTorusDualConfig L omega) *
          FK.fkWeight (triangularTorusGraph L) p q omega) *
          q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      ∑ omega,
        (p / (1 - BeffaraDC.dualParam p q)) ^
            (triangularTorusGraph L).edgeFinset.card *
          q ^ Nat.card (TorusSite L) *
          (F (triHexTorusDualConfig L omega) *
            FK.fkWeight (hexagonalTorusGraph L)
              (BeffaraDC.dualParam p q) q
              (triHexTorusDualConfig L omega) *
            q ^ triHexTorusDefect L
              (FK.openSub (triangularTorusGraph L) omega)) := by
        apply Finset.sum_congr rfl
        intro omega homega
        have h := triHexTorus_fkWeight_duality_signed L omega hp hp1 hq
        calc
          (F (triHexTorusDualConfig L omega) *
              FK.fkWeight (triangularTorusGraph L) p q omega) *
              q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
            F (triHexTorusDualConfig L omega) *
              (FK.fkWeight (triangularTorusGraph L) p q omega *
                q ^ ((triangularTorusGraph L).edgeFinset.card + 1)) := by ring
          _ = F (triHexTorusDualConfig L omega) *
              ((p / (1 - BeffaraDC.dualParam p q)) ^
                  (triangularTorusGraph L).edgeFinset.card *
                q ^ Nat.card (TorusSite L) *
                FK.fkWeight (hexagonalTorusGraph L)
                  (BeffaraDC.dualParam p q) q
                  (triHexTorusDualConfig L omega) *
                q ^ triHexTorusDefect L
                  (FK.openSub (triangularTorusGraph L) omega)) := by rw [h]
          _ = (p / (1 - BeffaraDC.dualParam p q)) ^
                (triangularTorusGraph L).edgeFinset.card *
              q ^ Nat.card (TorusSite L) *
              (F (triHexTorusDualConfig L omega) *
                FK.fkWeight (hexagonalTorusGraph L)
                  (BeffaraDC.dualParam p q) q
                  (triHexTorusDualConfig L omega) *
                q ^ triHexTorusDefect L
                  (FK.openSub (triangularTorusGraph L) omega)) := by ring
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        (∑ omega,
          F (triHexTorusDualConfig L omega) *
            FK.fkWeight (hexagonalTorusGraph L)
              (BeffaraDC.dualParam p q) q
              (triHexTorusDualConfig L omega) *
            q ^ triHexTorusDefect L
              (FK.openSub (triangularTorusGraph L) omega)) := by
      rw [Finset.mul_sum]

/-! ## E. Removing the topological weight -/

/-- For `q ≥ 1` the defect-weighted hexagonal partition function is between `Z` and `q² Z`. -/
lemma triHexTorus_defectWeighted_partition_bounds
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ≤
        triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q ∧
      triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q ≤
        q ^ 2 *
          triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hpDual0 := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  constructor
  · unfold triHexTorusDualPartitionSum
    unfold triHexTorusDefectWeightedDualPartitionSum
    apply Finset.sum_le_sum
    intro omega homega
    have hw := FK.fkWeight_nonneg (hexagonalTorusGraph L)
      hpDual0 hpDual1 hq0 (triHexTorusDualConfig L omega)
    have hd := (triHexTorus_topologicalCorrection_bounds L omega hq).1
    nlinarith
  · unfold triHexTorusDualPartitionSum
    unfold triHexTorusDefectWeightedDualPartitionSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    have hw := FK.fkWeight_nonneg (hexagonalTorusGraph L)
      hpDual0 hpDual1 hq0 (triHexTorusDualConfig L omega)
    have hd := (triHexTorus_topologicalCorrection_bounds L omega hq).2
    nlinarith

lemma triHexTorus_defectWeighted_numerator_bounds
    (L : ℕ) [Fact (2 < L)]
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    (hF : ∀ eta, 0 ≤ F eta) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F ≤
        triHexTorusDefectWeightedDualNumerator L
          (BeffaraDC.dualParam p q) q F ∧
      triHexTorusDefectWeightedDualNumerator L
          (BeffaraDC.dualParam p q) q F ≤
        q ^ 2 * triHexTorusDualNumerator L
          (BeffaraDC.dualParam p q) q F := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hpDual0 := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  constructor
  · unfold triHexTorusDualNumerator
    unfold triHexTorusDefectWeightedDualNumerator
    apply Finset.sum_le_sum
    intro omega homega
    have hw := FK.fkWeight_nonneg (hexagonalTorusGraph L)
      hpDual0 hpDual1 hq0 (triHexTorusDualConfig L omega)
    have hFw : 0 ≤ F (triHexTorusDualConfig L omega) *
        FK.fkWeight (hexagonalTorusGraph L)
          (BeffaraDC.dualParam p q) q
          (triHexTorusDualConfig L omega) :=
      mul_nonneg (hF _) hw
    have hd := (triHexTorus_topologicalCorrection_bounds L omega hq).1
    nlinarith
  · unfold triHexTorusDualNumerator
    unfold triHexTorusDefectWeightedDualNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    have hw := FK.fkWeight_nonneg (hexagonalTorusGraph L)
      hpDual0 hpDual1 hq0 (triHexTorusDualConfig L omega)
    have hFw : 0 ≤ F (triHexTorusDualConfig L omega) *
        FK.fkWeight (hexagonalTorusGraph L)
          (BeffaraDC.dualParam p q) q
          (triHexTorusDualConfig L omega) :=
      mul_nonneg (hF _) hw
    have hd := (triHexTorus_topologicalCorrection_bounds L omega hq).2
    nlinarith

/-- For `q ≥ 1` and `F ≥ 0` the defect-weighted hexagonal expectation is within a factor `q²` of the
plain one. -/
lemma triHexTorus_defectWeighted_normalized_bounds
    (L : ℕ) [Fact (2 < L)]
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    (hF : ∀ eta, 0 ≤ F eta) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpart : 0 < triHexTorusDualPartitionSum L
      (BeffaraDC.dualParam p q) q) :
    triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F /
          (q ^ 2 * triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q) ≤
        triHexTorusDefectWeightedDualNumerator L
            (BeffaraDC.dualParam p q) q F /
          triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q ∧
      triHexTorusDefectWeightedDualNumerator L
            (BeffaraDC.dualParam p q) q F /
          triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q ≤
        q ^ 2 * triHexTorusDualNumerator L
            (BeffaraDC.dualParam p q) q F /
          triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q := by
  let DN := triHexTorusDualNumerator L
    (BeffaraDC.dualParam p q) q F
  let WN := triHexTorusDefectWeightedDualNumerator L
    (BeffaraDC.dualParam p q) q F
  let DZ := triHexTorusDualPartitionSum L
    (BeffaraDC.dualParam p q) q
  let WZ := triHexTorusDefectWeightedDualPartitionSum L
    (BeffaraDC.dualParam p q) q
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq2 : 0 < q ^ 2 := pow_pos hq0 _
  have hN := triHexTorus_defectWeighted_numerator_bounds
    L F hF hp hp1 hq
  have hZ := triHexTorus_defectWeighted_partition_bounds L hp hp1 hq
  have hDN : 0 ≤ DN := by
    unfold DN triHexTorusDualNumerator
    apply Finset.sum_nonneg
    intro omega homega
    exact mul_nonneg (hF _) (FK.fkWeight_nonneg _
      (BeffaraDC.dualParam_pos hp hp1 hq0)
      (BeffaraDC.dualParam_lt_one hp hp1 hq0) hq0 _)
  have hWZ : 0 < WZ := lt_of_lt_of_le hpart hZ.1
  dsimp only [DN, WN, DZ, WZ] at hDN hWZ hN hZ ⊢
  constructor
  · rw [div_le_div_iff₀ (mul_pos hq2 hpart) hWZ]
    calc
      triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F *
          triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q ≤
        triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F *
          (q ^ 2 * triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q) :=
        mul_le_mul_of_nonneg_left hZ.2 hDN
      _ ≤ triHexTorusDefectWeightedDualNumerator L
            (BeffaraDC.dualParam p q) q F *
          (q ^ 2 * triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q) := by
        exact mul_le_mul_of_nonneg_right hN.1
          (mul_nonneg hq2.le hpart.le)
  · rw [div_le_div_iff₀ hWZ hpart]
    calc
      triHexTorusDefectWeightedDualNumerator L
            (BeffaraDC.dualParam p q) q F *
          triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q ≤
        (q ^ 2 * triHexTorusDualNumerator L
            (BeffaraDC.dualParam p q) q F) *
          triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q :=
        mul_le_mul_of_nonneg_right hN.2 hpart.le
      _ ≤ (q ^ 2 * triHexTorusDualNumerator L
            (BeffaraDC.dualParam p q) q F) *
          triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q := by
        exact mul_le_mul_of_nonneg_left hZ.1
          (mul_nonneg hq2.le hDN)

end PeriodicPlanar
end FK
end StatMech
