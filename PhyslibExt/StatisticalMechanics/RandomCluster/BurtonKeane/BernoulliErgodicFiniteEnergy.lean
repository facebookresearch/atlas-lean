/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Bernoulli
public import MathlibExt.Probability.Configuration.ProductMeasure
public import PhyslibExt.StatisticalMechanics.RandomCluster.Ergodicity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneZeroOrOne
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume

/-!
# Free lattice shifts and the boundary ratio

Lattice shifts act freely on sites, and the boundary of a box is negligible relative to its volume.

## i. Overview

Shifts act freely on sites (`bkc_smul_site_injective`). The box of radius `n` has a positive number
of sites (`bkc_boxFinsetBK_card_pos`), and its boundary has at most `2d/n` times as many
(`bkc_boundary_vol_ratio_le`), so the ratio tends to `0` (`bkc_boundary_vol_tendsto`).

## ii. Key results

- `bkc_boundary_vol_ratio_le` : the boundary-to-volume ratio is at most `2d/n`.
- `bkc_boundary_vol_tendsto` : the boundary-to-volume ratio tends to zero.

## iii. Table of contents

- A. Free shifts
- B. The boundary ratio

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open MeasureTheory Measure Set MeasurableSpace ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Free shifts -/

lemma bkc_smul_site_injective (a : Site d) :
    Function.Injective (fun g : Multiplicative (Site d) => g • a) := by
  intro g g' h
  apply Multiplicative.toAdd.injective
  funext i
  have := congrFun h i
  simp only [smul_site_apply] at this
  linarith

/-! ## B. The boundary ratio -/

lemma bkc_boxFinsetBK_card_pos (d n : ℕ) : 0 < (boxFinsetBK d n).card := by
  unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; positivity

lemma bkc_boundary_vol_ratio_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ) ≤ (2 * d : ℝ) / n := by
  have hboxcard : ((boxFinsetBK d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
    unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  set P : ℝ := (2 * (n : ℝ) + 1) ^ (d - 1) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  have hbound : (boxSV_boundaryCard d n : ℝ) ≤ 2 * (d * P) := by
    have hbR : (boxSV_boundaryCard d n : ℝ)
        = (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d := by
      rw [boxSV_boundary_card d n hn]
      have hle : (2 * n - 1) ^ d ≤ (2 * n + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      rw [Nat.cast_sub hle]
      congr 1
      · push_cast; ring
      · have h1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
          have : (1 : ℕ) ≤ 2 * n := by omega
          rw [Nat.cast_sub this]; push_cast; ring
        rw [← h1]; push_cast; ring_nf
    rw [hbR]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsub := boxSV_pow_sub_pow_le (2 * (n : ℝ) + 1) (2 * (n : ℝ) - 1)
      (by linarith) (by linarith) d
    calc (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d
        ≤ ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1)) * (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := hsub
      _ = 2 * (d * P) := by rw [hP]; ring
  have hpow : (2 * (n : ℝ) + 1) ^ d = (2 * (n : ℝ) + 1) * P := by
    rw [hP, ← pow_succ']; congr 1; omega
  rw [hboxcard, hpow, div_le_div_iff₀ (by positivity) (by exact_mod_cast hn)]
  calc (boxSV_boundaryCard d n : ℝ) * n ≤ 2 * (d * P) * n :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ ≤ 2 * d * ((2 * (n : ℝ) + 1) * P) := by
        have hle : (n : ℝ) ≤ 2 * (n : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ n by positivity]
        nlinarith [hP0, mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * d * P)]

lemma bkc_boundary_vol_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      atTop (𝓝 0) := by
  have hd0 : Tendsto (fun n : ℕ => (2 * d : ℝ) / n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 * d : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hd0
  filter_upwards [eventually_ge_atTop 1] with n hn using bkc_boundary_vol_ratio_le d n hd hn

end Percolation

end StatMech
