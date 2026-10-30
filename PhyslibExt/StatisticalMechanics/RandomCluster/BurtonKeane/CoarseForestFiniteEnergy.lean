/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxTrifSet
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifRemoveSites
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestProbCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryVolumeRatio

/-!
# Scale-zero coarse trifurcations and finite energy

At scale zero the coarse count is at most the boundary of the next box for every configuration, so
coarse trifurcations at scale zero have probability zero; with the coarse step this gives uniqueness
for Bernoulli percolation.

## i. Overview

The coarse count at scale zero equals the number of fine trifurcations in the next box, which is at
most the boundary of the box of radius `R + 1` for every configuration (`bfe_perConfig_count`). The
expectation is therefore bounded and, since the volume grows like `(2R + 1)^d`, the probability of a
scale-zero coarse trifurcation is zero and `μ(N = ⊤) = 0` given the coarse step. For Bernoulli
percolation with `p > 0`, the coarse step at scale zero gives uniqueness (`bfe_bk`).

**Fidelity.** The count and the probability-zero step are unconditional. `bfe_bk` is conditional on
the coarse trifurcation step `bc61_CoarseTrifExistence _ 0`.

## ii. Key results

- `bfe_perConfig_count` : the scale-zero coarse count, for every configuration.
- `bfe_bk` : uniqueness from the scale-zero coarse step.

## iii. Table of contents

- A. The scale-zero count
- B. Uniqueness

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. The scale-zero count -/

lemma bfe_coarseCount_eq_fineCount (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    bc61_coarseTcount ω 0 R = (bfin2_trifSet_finite ω (R + 1)).toFinset.card := by
  classical
  unfold bc61_coarseTcount
  congr 1
  apply Finset.ext
  intro y
  rw [bc61_mem_coarseTrifFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    bc67_coarseTrif_is_G_n_trifurcation ω 0 y]
  have hb : (R + 1) - 1 = R := by omega
  rw [hb]
  unfold bft_FineTrif
  exact and_comm

lemma bfe_perConfig_count (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard d (R + 1) := by
  rw [bfe_coarseCount_eq_fineCount ω R]
  calc (bfin2_trifSet_finite ω (R + 1)).toFinset.card
      ≤ (vertexBoundary_finite d (R + 1)).toFinset.card :=
        bfin2_count ω (R + 1) (Nat.succ_le_succ (Nat.zero_le R))
    _ = boxSV_boundaryCard d (R + 1) := rfl

lemma bfe_exp_eq (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (R : ℕ) :
    ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω 0 0}
      = ∫⁻ ω, (bc61_coarseTcount ω 0 R : ℝ≥0∞) ∂μ :=
  bc62_coarse_expectation μ hinv 0 R

lemma bfe_expBound (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (R : ℕ) :
    ∫⁻ ω, (bc61_coarseTcount ω 0 R : ℝ≥0∞) ∂μ ≤ (boxSV_boundaryCard d (R + 1) : ℝ≥0∞) := by
  calc ∫⁻ ω, (bc61_coarseTcount ω 0 R : ℝ≥0∞) ∂μ
      ≤ ∫⁻ _ω, (boxSV_boundaryCard d (R + 1) : ℝ≥0∞) ∂μ := by
        apply lintegral_mono; intro ω; exact Nat.cast_le.mpr (bfe_perConfig_count ω R)
    _ = (boxSV_boundaryCard d (R + 1) : ℝ≥0∞) := by
        rw [lintegral_const, measure_univ, mul_one]

lemma bfe_boxCard (R : ℕ) : ((boxFinsetBK d R).card : ℝ) = (2 * (R : ℝ) + 1) ^ d := by
  unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring

/-! ## B. Uniqueness -/

lemma bfe_dichotomy (hd : 1 ≤ d) (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    μ {ω | bc61_IsCoarseTrifurcation ω 0 0} = 0 :=
  bpe_coarseTrif_prob_eq_zero_of_expBound μ 0 (fun R => boxSV_boundaryCard d (R + 1))
    (fun R => bfe_exp_eq μ hinv R) (fun R => bfe_expBound μ R)
    (fun R => bkc_boxFinsetBK_card_pos d R) (StatMech.Walls.bc54_boundary_succ_vol_tendsto d hd)

lemma bfe_top_null (hd : 1 ≤ d) (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hexist : bc61_CoarseTrifExistence μ 0) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bpe_top_null_of_expCount μ 0 (fun R => boxSV_boundaryCard d (R + 1))
    (fun R => bfe_exp_eq μ hinv R) (fun R => bfe_expBound μ R)
    (fun R => bkc_boxFinsetBK_card_pos d R) (StatMech.Walls.bc54_boundary_succ_vol_tendsto d hd)
        hexist

/-- The coarse trifurcation step at scale zero for `μ`. -/
def bfe_finiteEnergy_residue (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  bc61_CoarseTrifExistence μ 0

/-- **Burton–Keane uniqueness from the scale-zero coarse step.** For Bernoulli bond percolation in
`d ≥ 1` with `p > 0`, if `N = ⊤` with positive probability gives a scale-zero coarse trifurcation at
the origin with positive probability, then a.s. `N ∈ {0, 1}`. Burton and Keane, *Density and
uniqueness in percolation* (1989). -/
lemma bfe_bk (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hexist : bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  have herg : IsErgodic (G := Multiplicative (Site d)) μ := bkc_bernoulli_isErgodic hd p hp1
  have hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ := herg.isTranslationInvariant
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := bfe_top_null hd μ hinv hexist
  exact bc120_uniqueness_of_top_null μ herg hfe htop

lemma bfe_bk_atLeastTwo (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hexist : bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  (bfe_bk hd p hp1 hp0 hexist).2.1

end StatMech.Walls
