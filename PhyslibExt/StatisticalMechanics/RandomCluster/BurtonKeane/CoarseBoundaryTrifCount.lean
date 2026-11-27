/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Algebra.Order.Field
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalHarmBox
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicForestJordanBridge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DecoupledForestCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalPrecursorFiniteEnergy
public import MathlibExt.Probability.Percolation.BurtonKeane.FiniteModification

/-!
# Classical trifurcations against the next boundary

The classical trifurcation count in a box is at most the boundary of the next box for every
configuration, so classical trifurcations have probability zero.

## i. Overview

Each classical trifurcation of the box of radius `n` has three arms through its open neighbours in
the box of radius `n + 1`, which reach its boundary in distinct sites. Hence
`bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1)` for every configuration, and the
boundary of the next box is negligible. So classical trifurcations have probability zero for every
translation-invariant measure in `d ≥ 1`, as `measure_encounter_eq_zero` states.

**Fidelity.** The classical count bound and probability zero are unconditional.

## ii. Key results

- `bc54_classicalTcount_le_boundary_succ_all` : the classical count against the next boundary, for
  every configuration.

## iii. Table of contents

- A. The classical count
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open MathlibExt.Probability.Percolation.BurtonKeaneWanted
  (IsEncounterPoint measure_encounter_eq_zero)

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. The classical count -/

lemma bc54_classicalTcount_le_boundary_succ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) :
    bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1) :=
  StatMech.Percolation.dfc_canonTcount_le_boundary_succ ω n hn

lemma bc54_classicalTcount_le_boundary_succ_all (ω : ConfigSpace (Sym2 (Site d))) (hd : 1 ≤ d)
    (n : ℕ) :
    bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    change ctc2_canonTcount d ω 0 ≤ boxSV_boundaryCard d (0 + 1)
    have h1 : ctc2_canonTcount d ω 0 ≤ 1 := by
      have hle : ctc2_canonTcount d ω 0 ≤ (boxFinsetBK d 0).card := by
        unfold ctc2_canonTcount; exact Finset.card_filter_le _ _
      have hc : (boxFinsetBK d 0).card = 1 := by
        unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; simp
      omega
    have h2 : 1 ≤ boxSV_boundaryCard d (0 + 1) := by
      rw [show (0 + 1) = 1 from rfl, boxSV_boundary_card d 1 (le_refl 1)]
      have he : (2 * 1 - 1) ^ d = 1 := by norm_num
      rw [he]
      have h3 : 3 ≤ (2 * 1 + 1) ^ d := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
          _ = (2 * 1 + 1) ^ d := by norm_num
      omega
    omega
  · exact bc54_classicalTcount_le_boundary_succ ω n hpos

lemma bc54_boundary_succ_vol_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ))
      atTop (𝓝 0) := by
  have hvol : ∀ n : ℕ, ((boxFinsetBK d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
    intro n; unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  have hvolpos : ∀ n : ℕ, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := by
    intro n; rw [hvol n]; positivity
  have hf : Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d (n + 1)).card :
      ℝ))
      atTop (𝓝 0) := (bkc_boundary_vol_tendsto d hd).comp (tendsto_add_atTop_nat 1)
  have hg : Tendsto (fun n => ((boxFinsetBK d (n + 1)).card : ℝ) / ((boxFinsetBK d n).card : ℝ))
      atTop (𝓝 1) := by
    have heq : (fun n => ((boxFinsetBK d (n + 1)).card : ℝ) / ((boxFinsetBK d n).card : ℝ))
        = (fun n : ℕ => ((2 * ((n : ℝ) + 1) + 1) / (2 * (n : ℝ) + 1)) ^ d) := by
      funext n; rw [hvol (n + 1), hvol n]; push_cast; rw [div_pow]
    rw [heq]
    have hbase : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1) + 1) / (2 * (n : ℝ) + 1)) atTop (𝓝 1) :=
        by
      have hrw : (fun n : ℕ => (2 * ((n : ℝ) + 1) + 1) / (2 * (n : ℝ) + 1))
          = (fun n : ℕ => 1 + 2 / (2 * (n : ℝ) + 1)) := by
        funext n
        have hne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
        rw [show (2 * ((n : ℝ) + 1) + 1) = (2 * (n : ℝ) + 1) + 2 by ring, add_div, div_self hne]
      rw [hrw]
      have h0 : Tendsto (fun n : ℕ => 2 / (2 * (n : ℝ) + 1)) atTop (𝓝 0) := by
        apply Filter.Tendsto.div_atTop tendsto_const_nhds
        apply Filter.tendsto_atTop_add_const_right
        exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds.add h0)
    have hp := hbase.pow d
    simpa using hp
  have hmul : Tendsto (fun n =>
      ((boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d (n + 1)).card : ℝ))
      * (((boxFinsetBK d (n + 1)).card : ℝ) / ((boxFinsetBK d n).card : ℝ)))
      atTop (𝓝 0) := by simpa using hf.mul hg
  have heq2 : (fun n =>
      ((boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d (n + 1)).card : ℝ))
      * (((boxFinsetBK d (n + 1)).card : ℝ) / ((boxFinsetBK d n).card : ℝ)))
      = (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ)) := by
    funext n
    have hne1 : ((boxFinsetBK d (n + 1)).card : ℝ) ≠ 0 := ne_of_gt (hvolpos (n + 1))
    field_simp
  rwa [heq2] at hmul

/-! ## B. Summary -/

lemma bc54_witness_boundary_trif_arm_inbox_succ :
    (![(2 : ℤ), 0] : Site 2) ∈ box 2 (1 + 1) :=
  bc53_harmbox_succ Bc53Witness.bwallConfig 1 (![(1 : ℤ), 0] : Site 2)
    Bc53Witness.bwall_hub_in_box Bc53Witness.bwall_isTrifurcation
    (![(2 : ℤ), 0] : Site 2) Bc53Witness.bwall_arm_adj Bc53Witness.bwall_arm_cut_infinite

lemma bc54_status (hd : 1 ≤ d) :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d (n + 1)) ∧
    (Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ))
      atTop (𝓝 0)) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ],
      IsTranslationInvariant (G := Multiplicative (Site d)) μ →
      μ {ω | IsEncounterPoint d ω 0} = 0) :=
  ⟨fun ω n => bc54_classicalTcount_le_boundary_succ_all ω hd n,
   bc54_boundary_succ_vol_tendsto d hd,
   fun μ _ hinv => measure_encounter_eq_zero μ hd hinv⟩

end StatMech.Walls
