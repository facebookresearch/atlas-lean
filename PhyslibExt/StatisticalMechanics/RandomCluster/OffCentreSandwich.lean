/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.FiniteVolumeShift
public import PhyslibExt.StatisticalMechanics.RandomCluster.DensityFiniteToInfinite
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxSurfaceRatio
/-!
# Off-centre sandwich for `q = 2` FK measures from rotation residues

Bulk edges of a large box are sandwiched between translated small boxes, which turns equality
of edge densities (rotation residues) into the off-centre sandwich used for FK uniqueness.

## i. Overview

Let `R = ⌊√n⌋`. Every edge of the inner box `Λ_{n-R}` is the translate by its first endpoint
`u` of a unit edge `{0, ±e_j}` of the small box `Λ_R`, and the translated box `u + Λ_R` lies in
`Λ_n`. By translation covariance and domination between nested boxes, the free marginal of the
edge in `Λ_n` is at least the free marginal of the unit edge in `Λ_R`, and (for the inner box
`Λ_{n-R-1}`, so that `u + Λ_R` avoids the boundary of `Λ_n`) the wired marginal is at most the
wired marginal in `Λ_R`. As `n → ∞` the small-box marginals of unit edges converge to their
infinite-volume densities, and the inner boxes contain all but a vanishing fraction
`O(d² √n / n)` of the edges of `Λ_n`.

The *rotation residue* for a box edge `e'` says that every lattice edge has the same density as
`e'`. Under it, the unit-edge marginals converge to the density of `e'`, which gives the off-centre
sandwiches `bdp_FreeOffCentreSandwich` and `bdp_WiredOffCentreSandwich`.

The residues are assumed for every `e' ∈ Sym2 Λ_N`, including non-edges such as `s(x, x)`, whose
density is `1/2`; so they cannot hold for `p < 1/2`.

## ii. Key results

- `ocs_edgeFinset_shell_fraction_tendsto_zero` : the edges outside an inner box `Λ_{m(n)}` form
  a vanishing fraction when `(n - m(n))/n → 0`.
- `ocs_free_offCentre_lower`, `ocs_wired_offCentre_upper` : comparison of bulk edge marginals in
  `Λ_n` with unit-edge marginals in `Λ_R`.
- `ocs_FreeRotationResidue`, `ocs_WiredRotationResidue` : the rotation residues.
- `ocs_freeOffCentreSandwich_of_rotation`, `ocs_wiredOffCentreSandwich_of_rotation` : the
  off-centre sandwiches from the residues.

## iii. Table of contents

- A. Edge counts of boxes and shells
  - A.1. Counting edges near a vertex set
  - A.2. Square-root inner boxes
- B. Translated small boxes inside large boxes
- C. Unit edges at the origin
- D. The free sandwich
- E. The wired sandwich

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.3 and §5.
- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, 2017.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}

/-!
## A. Edge counts of boxes and shells

### A.1. Counting edges near a vertex set
-/
lemma ocs_orderedEdges_firstIn_le (d n : ℕ) (S : Finset (Site d)) :
    ((boxSV_edgeF d n).filter (fun p => p.1 ∈ S)).card ≤ S.card * (2 * d) := by
  classical
  have hsub : (boxSV_edgeF d n).filter (fun p => p.1 ∈ S)
      ⊆ S.biUnion (fun x => (candFinset d x).image (fun y => (x, y))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpe, hpS⟩ := hp
    rw [boxSV_mem_edgeF] at hpe
    obtain ⟨_, _, hadj⟩ := hpe
    rw [Finset.mem_biUnion]
    refine ⟨p.1, hpS, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p.2, mem_candFinset_of_adj d p.1 p.2 hadj, by ext <;> rfl⟩
  calc ((boxSV_edgeF d n).filter (fun p => p.1 ∈ S)).card
      ≤ (S.biUnion (fun x => (candFinset d x).image (fun y => (x, y)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ x ∈ S, ((candFinset d x).image (fun y => (x, y))).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ S, (2 * d) := by
        apply Finset.sum_le_sum
        intro x _
        calc ((candFinset d x).image (fun y => (x, y))).card ≤ (candFinset d x).card :=
              Finset.card_image_le
          _ = 2 * d := card_candFinset d x
    _ = S.card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]

lemma ocs_orderedEdges_secondIn_le (d n : ℕ) (S : Finset (Site d)) :
    ((boxSV_edgeF d n).filter (fun p => p.2 ∈ S)).card ≤ S.card * (2 * d) := by
  classical
  have hsub : (boxSV_edgeF d n).filter (fun p => p.2 ∈ S)
      ⊆ S.biUnion (fun y => (candFinset d y).image (fun x => (x, y))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpe, hpS⟩ := hp
    rw [boxSV_mem_edgeF] at hpe
    obtain ⟨_, _, hadj⟩ := hpe
    rw [Finset.mem_biUnion]
    refine ⟨p.2, hpS, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p.1, mem_candFinset_of_adj d p.2 p.1 hadj.symm, by ext <;> rfl⟩
  calc ((boxSV_edgeF d n).filter (fun p => p.2 ∈ S)).card
      ≤ (S.biUnion (fun y => (candFinset d y).image (fun x => (x, y)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ y ∈ S, ((candFinset d y).image (fun x => (x, y))).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ S, (2 * d) := by
        apply Finset.sum_le_sum
        intro y _
        calc ((candFinset d y).image (fun x => (x, y))).card ≤ (candFinset d y).card :=
              Finset.card_image_le
          _ = 2 * d := card_candFinset d y
    _ = S.card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]

lemma ocs_edgeF_mono {d m n : ℕ} (h : m ≤ n) : boxSV_edgeF d m ⊆ boxSV_edgeF d n := by
  intro p hp
  rw [boxSV_mem_edgeF] at hp ⊢
  exact ⟨boxSV_boxF_subset d h hp.1, boxSV_boxF_subset d h hp.2.1, hp.2.2⟩

lemma ocs_edgeCard_sub_le (d : ℕ) {m n : ℕ} (h : m ≤ n) :
    boxSV_edgeCard d n - boxSV_edgeCard d m
      ≤ 4 * d * (boxSV_boxF d n \ boxSV_boxF d m).card := by
  classical
  set shell := boxSV_boxF d n \ boxSV_boxF d m with hshell
  have hsubdiff : boxSV_edgeF d n \ boxSV_edgeF d m
      ⊆ (boxSV_edgeF d n).filter (fun p => p.1 ∈ shell)
        ∪ (boxSV_edgeF d n).filter (fun p => p.2 ∈ shell) := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpn, hpm⟩ := hp
    rw [boxSV_mem_edgeF] at hpn
    obtain ⟨h1n, h2n, hadj⟩ := hpn
    have hnotboth : p.1 ∉ boxSV_boxF d m ∨ p.2 ∉ boxSV_boxF d m := by
      by_contra hc
      push Not at hc
      exact hpm (boxSV_mem_edgeF.mpr ⟨hc.1, hc.2, hadj⟩)
    rw [Finset.mem_union]
    rcases hnotboth with h1 | h2
    · left; rw [Finset.mem_filter]; exact ⟨boxSV_mem_edgeF.mpr ⟨h1n, h2n, hadj⟩,
        Finset.mem_sdiff.mpr ⟨h1n, h1⟩⟩
    · right; rw [Finset.mem_filter]; exact ⟨boxSV_mem_edgeF.mpr ⟨h1n, h2n, hadj⟩,
        Finset.mem_sdiff.mpr ⟨h2n, h2⟩⟩
  have hdiffcard : (boxSV_edgeF d n \ boxSV_edgeF d m).card
      = (boxSV_edgeF d n).card - (boxSV_edgeF d m).card :=
    Finset.card_sdiff_of_subset (ocs_edgeF_mono h)
  change (boxSV_edgeF d n).card - (boxSV_edgeF d m).card ≤ 4 * d * shell.card
  calc (boxSV_edgeF d n).card - (boxSV_edgeF d m).card
      = (boxSV_edgeF d n \ boxSV_edgeF d m).card := hdiffcard.symm
    _ ≤ ((boxSV_edgeF d n).filter (fun p => p.1 ∈ shell)
          ∪ (boxSV_edgeF d n).filter (fun p => p.2 ∈ shell)).card := Finset.card_le_card hsubdiff
    _ ≤ ((boxSV_edgeF d n).filter (fun p => p.1 ∈ shell)).card
          + ((boxSV_edgeF d n).filter (fun p => p.2 ∈ shell)).card := Finset.card_union_le _ _
    _ ≤ shell.card * (2 * d) + shell.card * (2 * d) :=
        Nat.add_le_add (ocs_orderedEdges_firstIn_le d n shell)
          (ocs_orderedEdges_secondIn_le d n shell)
    _ = 4 * d * shell.card := by ring

/-!
### A.2. Square-root inner boxes
-/
lemma ocs_sqrt_tendsto_atTop : Tendsto (fun n : ℕ => Nat.sqrt n) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b * b, fun n hn => ?_⟩
  calc b = Nat.sqrt (b * b) := (Nat.sqrt_eq b).symm
    _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn

lemma ocs_inv_sqrt_to_zero : Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ocs_sqrt_tendsto_atTop
  exact h1.inv_tendsto_atTop.congr (fun n => by simp [one_div])

lemma ocs_sqrt_div_to_zero : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ ocs_inv_sqrt_to_zero
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  have hsq : (Nat.sqrt n) * (Nat.sqrt n) ≤ n := by
    have := Nat.sqrt_le' n
    calc (Nat.sqrt n) * (Nat.sqrt n) = (Nat.sqrt n) ^ 2 := by ring
      _ ≤ n := this
  have hsR : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [div_le_div_iff₀ hnR hsR]
  calc (Nat.sqrt n : ℝ) * (Nat.sqrt n) = ((Nat.sqrt n * Nat.sqrt n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (n : ℝ) := by exact_mod_cast hsq
    _ = 1 * n := by ring

/-- The fraction of ordered edges of `Λ_n` outside `Λ_m` is at most `4 d² (n - m)/n`. -/
lemma ocs_edgeCard_shell_fraction_le (d : ℕ) (hd : 1 ≤ d) (n m : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) :
    ((boxSV_edgeCard d n - boxSV_edgeCard d m : ℕ) : ℝ) / (boxSV_edgeCard d n)
      ≤ 4 * (d : ℝ) ^ 2 * (((n - m : ℕ) : ℝ) / n) := by
  have hnm2 : 2 * (n : ℝ) - 2 * m = 2 * ((n - m : ℕ) : ℝ) := by rw [Nat.cast_sub hmn]; ring
  have hnum_nat : boxSV_edgeCard d n - boxSV_edgeCard d m
      ≤ 4 * d * (boxSV_boxF d n \ boxSV_boxF d m).card := ocs_edgeCard_sub_le d hmn
  have hshellcard : (boxSV_boxF d n \ boxSV_boxF d m).card = (2 * n + 1) ^ d - (2 * m + 1) ^ d := by
    rw [Finset.card_sdiff_of_subset (boxSV_boxF_subset d hmn), boxSV_card_boxF, boxSV_card_boxF]
  have hden_nat : (2 * n) * (2 * n + 1) ^ (d - 1) ≤ boxSV_edgeCard d n := boxSV_edge_card_lower hd
  have hden_pos : (0 : ℝ) < boxSV_edgeCard d n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hcast : (((2 * n) * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ)
        = (2 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ (d - 1) := by push_cast; ring
    calc (0 : ℝ) < (2 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ (d - 1) := by positivity
      _ = (((2 * n) * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := hcast.symm
      _ ≤ (boxSV_edgeCard d n : ℝ) := by exact_mod_cast hden_nat
  have hnum_real : ((boxSV_edgeCard d n - boxSV_edgeCard d m : ℕ) : ℝ)
      ≤ 4 * d * ((2 * (n : ℝ) - 2 * m) * (d * (2 * (n : ℝ) + 1) ^ (d - 1))) := by
    have hcast : ((4 * d * (boxSV_boxF d n \ boxSV_boxF d m).card : ℕ) : ℝ)
        = 4 * d * ((boxSV_boxF d n \ boxSV_boxF d m).card : ℝ) := by push_cast; ring
    calc ((boxSV_edgeCard d n - boxSV_edgeCard d m : ℕ) : ℝ)
        ≤ ((4 * d * (boxSV_boxF d n \ boxSV_boxF d m).card : ℕ) : ℝ) := by exact_mod_cast hnum_nat
      _ = 4 * d * ((boxSV_boxF d n \ boxSV_boxF d m).card : ℝ) := hcast
      _ ≤ 4 * d * (((2 * n + 1) ^ d - (2 * m + 1) ^ d : ℕ) : ℝ) := by rw [hshellcard]
      _ ≤ 4 * d * ((2 * (n : ℝ) - 2 * m) * (d * (2 * (n : ℝ) + 1) ^ (d - 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hle : (2 * m + 1) ^ d ≤ (2 * n + 1) ^ d := Nat.pow_le_pow_left (by omega) d
            rw [Nat.cast_sub hle]
            have hc1 : (((2 * n + 1) ^ d : ℕ) : ℝ) = (2 * (n : ℝ) + 1) ^ d := by push_cast; ring
            have hc2 : (((2 * m + 1) ^ d : ℕ) : ℝ) = (2 * (m : ℝ) + 1) ^ d := by push_cast; ring
            rw [hc1, hc2]
            have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
            have := boxSV_pow_sub_pow_le (2 * (n : ℝ) + 1) (2 * (m : ℝ) + 1)
              (by positivity) (by linarith) d
            calc (2 * (n : ℝ) + 1) ^ d - (2 * (m : ℝ) + 1) ^ d
                ≤ ((2 * (n : ℝ) + 1) - (2 * (m : ℝ) + 1))
                  * (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := this
              _ = (2 * (n : ℝ) - 2 * m) * (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := by ring
  rw [div_le_iff₀ hden_pos]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc ((boxSV_edgeCard d n - boxSV_edgeCard d m : ℕ) : ℝ)
      ≤ 4 * d * ((2 * (n : ℝ) - 2 * m) * (d * (2 * (n : ℝ) + 1) ^ (d - 1))) := hnum_real
    _ = 4 * d * ((2 * ((n - m : ℕ) : ℝ)) * (d * (2 * (n : ℝ) + 1) ^ (d - 1))) := by rw [hnm2]
    _ = 8 * (d : ℝ) ^ 2 * ((n - m : ℕ) : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) := by ring
    _ = 4 * (d : ℝ) ^ 2 * (((n - m : ℕ) : ℝ) / n)
          * (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1)) := by
          field_simp; ring
    _ ≤ 4 * (d : ℝ) ^ 2 * (((n - m : ℕ) : ℝ) / n) * (boxSV_edgeCard d n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hcast : (((2 * n) * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ)
              = (2 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ (d - 1) := by push_cast; ring
          calc (2 * (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1))
              = (((2 * n) * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := by rw [hcast]
            _ ≤ (boxSV_edgeCard d n : ℝ) := by exact_mod_cast hden_nat

lemma ocs_gap_sub_tendsto_zero :
    Tendsto (fun n => ((n - (n - Nat.sqrt n) : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  refine ocs_sqrt_div_to_zero.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : n - (n - Nat.sqrt n) = Nat.sqrt n := by
    have := Nat.sqrt_le_self n; omega
  rw [this]

lemma ocs_gap_sub_one_tendsto_zero :
    Tendsto (fun n => ((n - (n - Nat.sqrt n - 1) : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hbound : Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have h := ocs_sqrt_div_to_zero.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h
    refine h.congr (fun n => ?_)
    by_cases hn : (n : ℝ) = 0
    · rw [hn]; simp
    · field_simp
  refine hbound.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hs1 : Nat.sqrt n + 1 ≤ n := by
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := by
      have := Nat.sqrt_le' n
      calc Nat.sqrt n * Nat.sqrt n = (Nat.sqrt n) ^ 2 := by ring
        _ ≤ n := this
    nlinarith [Nat.sqrt_le_self n, h2]
  have : n - (n - Nat.sqrt n - 1) = Nat.sqrt n + 1 := by omega
  rw [this]; push_cast; ring

/-- If `(n - m(n))/n → 0`, the edges of `Λ_n` outside `Λ_{m(n)}` form a vanishing fraction of
the edges of `Λ_n`. -/
lemma ocs_edgeFinset_shell_fraction_tendsto_zero (d : ℕ) (hd : 1 ≤ d) (m : ℕ → ℕ)
    (hm : ∀ n, m n ≤ n) (hgap : Tendsto (fun n => ((n - m n : ℕ) : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n => (((boxGraph d n).edgeFinset.card
          - (boxGraph d (m n)).edgeFinset.card : ℝ))
        / (boxGraph d n).edgeFinset.card) atTop (𝓝 0) := by
  have hgoal : Tendsto (fun n =>
      ((boxSV_edgeCard d n - boxSV_edgeCard d (m n) : ℕ) : ℝ) / (boxSV_edgeCard d n))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 4 * (d : ℝ) ^ 2 * (((n - m n : ℕ) : ℝ) / n)) atTop (𝓝 0) := by
      have := hgap.const_mul (4 * (d : ℝ) ^ 2); simpa using this
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_ge_atTop 1] with n hn; positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact ocs_edgeCard_shell_fraction_le d hd n (m n) hn (hm n)
  refine hgoal.congr' ?_
  filter_upwards with n
  have hen := fup_edge_card_eq d n
  have hle : boxSV_edgeCard d (m n) ≤ boxSV_edgeCard d n := by
    unfold boxSV_edgeCard; exact Finset.card_le_card (ocs_edgeF_mono (hm n))
  have hem := fup_edge_card_eq d (m n)
  have hee : ((boxSV_edgeCard d n - boxSV_edgeCard d (m n) : ℕ) : ℝ)
      = 2 * (((boxGraph d n).edgeFinset.card : ℝ)
          - (boxGraph d (m n)).edgeFinset.card) := by
    rw [Nat.cast_sub hle, hen, hem]; push_cast; ring
  have hden : ((boxSV_edgeCard d n : ℕ) : ℝ) = 2 * ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [hen]; push_cast; ring
  rw [hee, hden]
  by_cases hE : ((boxGraph d n).edgeFinset.card : ℝ) = 0
  · simp [hE]
  · field_simp

/-!
## B. Translated small boxes inside large boxes
-/
lemma ocs_innerEdge_recentre (d R n md : ℕ) (hmn : md ≤ n) (u v : boxVerts d md)
    (hsub : fvs_transBox d R ((u : Site d)) ⊆ box d n)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    ocd_innerEdge (flc_incl hsub)
        (Sym2.map (fvs_transEquiv d R (u : Site d))
          (s((⟨(0 : Site d), c0⟩ : boxVerts d R),
            (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))))
      = innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d md)) := by
  apply Sym2.map.injective (Subtype.val_injective (p := fun y => y ∈ box d n))
  rw [ocd_innerEdge]
  simp only [innerEdgeLE, Sym2.map_mk]
  congr 1
  · change ((flc_incl hsub (fvs_transEquiv d R (u : Site d) ⟨(0 : Site d), c0⟩)) : Site d)
        = ((boxVertInclLE d hmn u) : Site d)
    rw [flc_incl_val]
    rw [fvs_transEquiv_val]; simp [boxVertInclLE]
  · change ((flc_incl hsub
        (fvs_transEquiv d R (u : Site d) ⟨(v : Site d) - (u : Site d), cw⟩)) : Site d)
        = ((boxVertInclLE d hmn v) : Site d)
    rw [flc_incl_val, fvs_transEquiv_val]; simp [boxVertInclLE]

/-- For `u, v` adjacent in `Λ_{n-R}`, the free marginal in `Λ_n` of the edge `{u, v}` is at least
the free marginal in `Λ_R` of the recentered edge `{0, v - u}`. -/
lemma ocs_free_offCentre_lower (d R n : ℕ) (hRn : R ≤ n) (hmn : n - R ≤ n)
    (u v : boxVerts d (n - R)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    edgeMargProb (fkProb (boxGraph d R) p 2)
        (s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)))
      ≤ edgeMargProb (fkProb (boxGraph d n) p 2)
          (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R)))) := by
  set a : Site d := (u : Site d) with ha
  have ha_box : a ∈ box d (n - R) := u.2
  have hsub : fvs_transBox d R a ⊆ box d n := by
    intro y hy
    have hy' : (y - a) ∈ box d R := hy
    intro i
    have hyi : ((y - a) i).natAbs ≤ R := hy' i
    have hai : (a i).natAbs ≤ n - R := ha_box i
    have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
    have hyeq : y i = (y i - a i) + a i := by ring
    calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
      _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R) := Nat.add_le_add hyi hai
      _ = n := by omega
  set ce : Sym2 (boxVerts d R) :=
    s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))
    with hce
  have htrans := (fvs_box_translation_edgeMarg d R a ce (p := p) (q := 2)).2
  set eS : Sym2 (fvs_transBoxVerts d R a) := Sym2.map (fvs_transEquiv d R a) ce with heS
  have hdom := bdp_latticeFree_multiMass_dominated (Sin := fvs_transBox d R a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub) hp hp1
    (by norm_num : (1 : ℝ) ≤ 2) ({eS} : Finset (Sym2 (fvs_transBoxVerts d R a)))
  rw [Finset.image_singleton] at hdom
  rw [← bdp_edgeMargProb_eq_med_singleton, ← bdp_edgeMargProb_eq_med_singleton] at hdom
  rw [show edgeMargProb (fkProb (boxGraph d R) p 2) ce
        = edgeMargProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p 2) eS
      from htrans.symm]
  refine hdom.trans (le_of_eq ?_)
  congr 1
  exact ocs_innerEdge_recentre d R n (n - R) hmn u v hsub c0 cw

lemma ocs_wired_margin (d R n : ℕ) (a : Site d) (ha : a ∈ box d (n - R - 1)) (hRn : R + 1 ≤ n)
    (hsub : fvs_transBox d R a ⊆ box d n)
    (x : {y : Site d // y ∈ fvs_transBox d R a}) :
    ¬ boxBoundary d n (flc_incl hsub x) := by
  intro hbd
  have hxbox : (x : Site d) ∈ box d (n - 1) := by
    intro i
    have hxiR : (((x : Site d) - a) i).natAbs ≤ R := x.2 i
    have hai : (a i).natAbs ≤ n - R - 1 := ha i
    have hsubc : ((x : Site d) - a) i = (x : Site d) i - a i := by simp [Pi.sub_apply]
    have hxeq : (x : Site d) i = ((x : Site d) i - a i) + a i := by ring
    calc ((x : Site d) i).natAbs = (((x : Site d) i - a i) + a i).natAbs := by rw [← hxeq]
      _ ≤ ((x : Site d) i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = (((x : Site d) - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R - 1) := Nat.add_le_add hxiR hai
      _ ≤ n - 1 := by omega
  exact (hbd.2) hxbox

/-- For `u, v` adjacent in `Λ_{n-R-1}` and `R ≥ 1`, the wired marginal in `Λ_n` of `{u, v}` is at
most the wired marginal in `Λ_R` of the recentered edge `{0, v - u}`. -/
lemma ocs_wired_offCentre_upper (d R n : ℕ) (hR : 1 ≤ R) (hRn1 : R + 1 ≤ n) (hmn : n - R - 1 ≤ n)
    (u v : boxVerts d (n - R - 1)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2)
        (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R - 1))))
      ≤ edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p 2)
          (s((⟨(0 : Site d), c0⟩ : boxVerts d R),
            (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) := by
  set a : Site d := (u : Site d) with ha
  have ha_box : a ∈ box d (n - R - 1) := u.2
  have hsub : fvs_transBox d R a ⊆ box d n := by
    intro y hy
    have hy' : (y - a) ∈ box d R := hy
    intro i
    have hyi : ((y - a) i).natAbs ≤ R := hy' i
    have hai : (a i).natAbs ≤ n - R - 1 := ha_box i
    have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
    have hyeq : y i = (y i - a i) + a i := by ring
    calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
      _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R - 1) := Nat.add_le_add hyi hai
      _ ≤ n := by omega
  set ce : Sym2 (boxVerts d R) :=
    s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))
    with hce
  have htrans := (fvs_box_translation_edgeMarg d R a ce (p := p) (q := 2)).1
  set eS : Sym2 (fvs_transBoxVerts d R a) := Sym2.map (fvs_transEquiv d R a) ce with heS
  have hdom := ocd_latticeWired_multiMass_dominated (Sin := fvs_transBox d R a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d n) (fvs_transBoxBoundary d R a)
    (ocs_wired_margin d R n a ha_box hRn1 hsub)
    (flc_hbdryIn_transBox hR a)
    hp hp1 (by norm_num : (1 : ℝ) ≤ 2) ({eS} : Finset (Sym2 (fvs_transBoxVerts d R a)))
  rw [Finset.image_singleton] at hdom
  rw [← bdp_edgeMargProb_eq_med_singleton, ← bdp_edgeMargProb_eq_med_singleton] at hdom
  rw [show edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p 2) ce
        = edgeMargProb (wiredFkProb (fvs_transBoxGraph d R a) (fvs_transBoxBoundary d R a) p 2) eS
      from htrans.symm]
  refine le_trans (le_of_eq ?_) hdom
  congr 1
  exact (ocs_innerEdge_recentre d R n (n - R - 1) hmn u v hsub c0 cw).symm

/-!
## C. Unit edges at the origin
-/
lemma ocs_zero_mem_box (d R : ℕ) : (0 : Site d) ∈ box d R := by intro i; simp

lemma ocs_candMap_mem_box (d R : ℕ) (hR : 1 ≤ R) (p : Fin d × Bool) :
    candMap d (0 : Site d) p ∈ box d R := by
  intro i
  change (Function.update (0 : Site d) p.1
    ((0 : Site d) p.1 + (if p.2 then 1 else -1)) i).natAbs ≤ R
  by_cases hi : i = p.1
  · subst hi; rw [Function.update_self]; simp only [Pi.zero_apply, zero_add]
    rcases hp2 : p.2 <;> simp <;> omega
  · rw [Function.update_of_ne hi]; simp

/-- The difference of adjacent box vertices is a signed unit vector. See also `rot_edge_dir`. -/
lemma ocs_edge_dir_candMap (d m : ℕ) (u v : boxVerts d m) (hadj : (boxGraph d m).Adj u v) :
    ∃ p : Fin d × Bool, (v : Site d) - (u : Site d) = candMap d (0 : Site d) p := by
  rw [boxGraph, SimpleGraph.comap_adj] at hadj
  change NearestNeighbour d (u : Site d) (v : Site d) at hadj
  rw [nearestNeighbour_iff_shift] at hadj
  obtain ⟨j, s, hs, hvs⟩ := hadj
  refine ⟨(j, decide (s = 1)), ?_⟩
  funext i
  rw [hvs]
  change (Function.update (u : Site d) j ((u : Site d) j + s) i - (u : Site d) i)
      = Function.update (0 : Site d) j ((0 : Site d) j + (if decide (s = 1) then 1 else -1)) i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, Function.update_self]
    simp only [Pi.zero_apply, zero_add]
    rcases hs with rfl | rfl <;> simp
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]; simp

/-- The unit edge `{0, ±e_j}` of the box `Λ_R`, `R ≥ 1`, indexed by `(j, sign)`. -/
def ocs_unitEdge (d R : ℕ) (hR : 1 ≤ R) (p : Fin d × Bool) : Sym2 (boxVerts d R) :=
  s((⟨(0 : Site d), ocs_zero_mem_box d R⟩ : boxVerts d R),
    (⟨candMap d (0 : Site d) p, ocs_candMap_mem_box d R hR p⟩ : boxVerts d R))

lemma ocs_unitEdge_eq_innerEdgeLE (d r : ℕ) (hr : 1 ≤ r) (p : Fin d × Bool) :
    ocs_unitEdge d r hr p = innerEdgeLE d hr (ocs_unitEdge d 1 (le_refl 1) p) := by
  unfold ocs_unitEdge innerEdgeLE
  rw [Sym2.map_mk]; congr 1

lemma ocs_unitEdge1_mem_edgeFinset (d : ℕ) (p : Fin d × Bool) :
    ocs_unitEdge d 1 (le_refl 1) p ∈ (boxGraph d 1).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  change (boxGraph d 1).Adj _ _
  rw [boxGraph, SimpleGraph.comap_adj]
  change NearestNeighbour d (0 : Site d) (candMap d (0 : Site d) p)
  exact adj_candMap d (0 : Site d) p

set_option maxHeartbeats 1500000 in
-- elaborating the dependent `if hR : 1 ≤ Nat.sqrt n` family and its `congrArg` transport
-- exceeds the default budget
/-- The free marginal of a unit edge in `Λ_{⌊√n⌋}` converges to its free `q = 2` density. -/
lemma ocs_unitEdge_marg_tendsto (d : ℕ) (p : Fin d × Bool) {pr : ℝ} (hp : 0 < pr) (hp1 : pr < 1) :
    Tendsto (fun n =>
        if hR : 1 ≤ Nat.sqrt n then
          edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) pr 2) (ocs_unitEdge d (Nat.sqrt n) hR p)
        else (0 : ℝ)) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) pr)) := by
  have hbase := dfi_free_density_eq_limit 1 (ocs_unitEdge d 1 (le_refl 1) p) hp hp1
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  have hcomp := hbase.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, dite_eq_left hR]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR p]
  exact congrArg (fun s : {s : ℕ // 1 ≤ s} =>
    edgeMargProb (fkProb (boxGraph d s.1) pr 2)
      (innerEdgeLE d s.2 (ocs_unitEdge d 1 (le_refl 1) p)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {s : ℕ // 1 ≤ s}) = ⟨Nat.sqrt n, hR⟩ from
      Subtype.ext hrr)

/-!
## D. The free sandwich
-/

/-- The free rotation residue at tilt `t` for the box pair `e'`: every lattice edge of every box
has the free `q = 2` density of `e'` at `p = logistic t`. -/
def ocs_FreeRotationResidue (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) : Prop :=
  ∀ (m : ℕ) (eb : Sym2 (boxVerts d m)), eb ∈ (boxGraph d m).edgeFinset →
    freeEdgeDensity d 2 (edgeIncl d m eb) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)

/-- The free marginal at `p = logistic t` of the unit edge `(j, sign)` in `Λ_{⌊√n⌋}`, and `0`
when `⌊√n⌋ = 0`. -/
noncomputable def ocs_unitMarg (d n : ℕ) (p : Fin d × Bool) (t : ℝ) : ℝ :=
  if hR : 1 ≤ Nat.sqrt n then
    edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) 2)
      (ocs_unitEdge d (Nat.sqrt n) hR p)
  else 0

/-- The total deviation `∑_{(j, sign)} |density(e') - unit-edge marginal|` of the free unit-edge
marginals in `Λ_{⌊√n⌋}` from the free density of `e'`. -/
noncomputable def ocs_freeDelta (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ p : Fin d × Bool,
    |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|

lemma ocs_freeDelta_nonneg (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) :
    0 ≤ ocs_freeDelta N e' t n :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma ocs_perDir_tendsto_zero (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_FreeRotationResidue (d := d) N e' t) (p : Fin d × Bool) :
    Tendsto (fun n => |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)
        - ocs_unitMarg d n p t|) atTop (𝓝 0) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hconv := ocs_unitEdge_marg_tendsto d p hp hp1
  have hLeq : freeEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
    hres 1 (ocs_unitEdge d 1 (le_refl 1) p) (ocs_unitEdge1_mem_edgeFinset d p)
  rw [hLeq] at hconv
  have hmt : Tendsto (fun n => ocs_unitMarg d n p t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := hconv.congr (fun n => rfl)
  have hsub := (tendsto_const_nhds
    (x := freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))).sub hmt
  rw [sub_self] at hsub
  have := hsub.abs
  rwa [abs_zero] at this

lemma ocs_freeDelta_tendsto_zero (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_FreeRotationResidue (d := d) N e' t) :
    Tendsto (fun n => ocs_freeDelta N e' t n) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ p : Fin d × Bool,
      |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|)
      atTop (𝓝 (∑ p : Fin d × Bool, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun p _ => ocs_perDir_tendsto_zero N e' t hres p)
  rw [Finset.sum_const_zero] at h
  exact h

lemma ocs_innerEdgeLE_mem_edgeFinset (d : ℕ) {m n : ℕ} (h : m ≤ n) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) :
    innerEdgeLE d h eb ∈ (boxGraph d n).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at heb ⊢
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    rw [innerEdgeLE, Sym2.map_mk, SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj]
    exact heb

/-- The bulk edges of `Λ_n`: the edges of the inner box `Λ_{n - ⌊√n⌋}`. -/
noncomputable def ocs_bulkSet (d n : ℕ) : Finset (Sym2 (boxVerts d n)) :=
  (boxGraph d (n - Nat.sqrt n)).edgeFinset.image (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)))

/-- Every bulk edge of `Λ_n` has free marginal at least `density(e') - ocs_freeDelta`. -/
lemma ocs_free_bulk_lower (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n)) (hadj : (boxGraph d (n - Nat.sqrt n)).Adj u v) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_freeDelta N e' t n
      ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2)
          (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n))
            (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n)))) := by
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  have hRn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have hmn : n - Nat.sqrt n ≤ n := Nat.sub_le n (Nat.sqrt n)
  obtain ⟨p0, hp0⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hp0]; exact ocs_candMap_mem_box d (Nat.sqrt n) hR p0
  have hlow := ocs_free_offCentre_lower d (Nat.sqrt n) n hRn hmn u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
        (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n))))
      = ocs_unitEdge d (Nat.sqrt n) hR p0 := by
    unfold ocs_unitEdge; congr 1; exact Subtype.ext hp0
  rw [hue] at hlow
  have hmarg : ocs_unitMarg d n p0 t
      = edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) 2)
          (ocs_unitEdge d (Nat.sqrt n) hR p0) := by
    unfold ocs_unitMarg; rw [dite_eq_left hR]
  have hterm : |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p0 t|
      ≤ ocs_freeDelta N e' t n :=
    Finset.single_le_sum
      (f := fun p =>
        |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ p0)
  have h1 : freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_freeDelta N e' t n
      ≤ ocs_unitMarg d n p0 t := by
    have h2 : freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p0 t
        ≤ ocs_freeDelta N e' t n := le_trans (le_abs_self _) hterm
    linarith
  rw [hmarg] at h1
  exact le_trans h1 hlow

/-- The free off-centre sandwich from the free rotation residues for all pairs `e'` of `Λ_N`. -/
lemma ocs_freeOffCentreSandwich_of_rotation (hd : 1 ≤ d) (N : ℕ)
    (hres : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t) :
    bdp_FreeOffCentreSandwich (d := d) N := by
  intro e' t
  refine ⟨ocs_bulkSet d, ocs_freeDelta N e' t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => ocs_freeDelta_nonneg N e' t n
  · exact ocs_freeDelta_tendsto_zero N e' t (hres e' t)
  · intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [edgeIncl_innerEdgeLE]
    exact hres e' t (n - Nat.sqrt n) eb heb
  · intro n e he
    rw [ocs_bulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at heb
    by_cases hn : 1 ≤ n
    · induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        exact ocs_free_bulk_lower N e' t n hn u v heb
    · exfalso
      have hn0 : n = 0 := by omega
      subst hn0
      induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        have huv : (u : Site d) = (v : Site d) := by
          have hu := u.2; have hv := v.2
          funext i
          have h1 := hu i; have h2 := hv i
          simp only [Nat.zero_sub] at h1 h2; omega
        rw [boxGraph, SimpleGraph.comap_adj] at heb
        change NearestNeighbour d (u : Site d) (v : Site d) at heb
        rw [huv] at heb
        rw [show NearestNeighbour d (v : Site d) (v : Site d)
              ↔ (∑ i, ((v : Site d) i - (v : Site d) i).natAbs) = 1 from Iff.rfl] at heb
        simp at heb
  · have hcard : ∀ n, (ocs_bulkSet d n).card = (boxGraph d (n - Nat.sqrt n)).edgeFinset.card :=
      fun n => Finset.card_image_of_injective _
        (dfi_innerEdgeLE_injective d (Nat.sub_le n (Nat.sqrt n)))
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd (fun n => n - Nat.sqrt n)
      (fun n => Nat.sub_le n _) ocs_gap_sub_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]

/-!
## E. The wired sandwich
-/

set_option maxHeartbeats 1500000 in
-- elaborating the dependent `if hR : 1 ≤ Nat.sqrt n` family and its `congrArg` transport
-- exceeds the default budget
/-- The wired marginal of a unit edge in `Λ_{⌊√n⌋}` converges to its wired `q = 2` density. -/
lemma ocs_unitEdge_wired_marg_tendsto (d : ℕ) (p : Fin d × Bool) {pr : ℝ}
    (hp : 0 < pr) (hp1 : pr < 1) :
    Tendsto (fun n =>
        if hR : 1 ≤ Nat.sqrt n then
          edgeMargProb (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n)) pr 2)
            (ocs_unitEdge d (Nat.sqrt n) hR p)
        else (0 : ℝ)) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) pr)) := by
  have hbase := dfi_wired_density_eq_limit 1 (ocs_unitEdge d 1 (le_refl 1) p) hp hp1
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  have hcomp := hbase.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, dite_eq_left hR]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR p]
  exact congrArg (fun s : {s : ℕ // 1 ≤ s} =>
    edgeMargProb (wiredFkProb (boxGraph d s.1) (boxBoundary d s.1) pr 2)
      (innerEdgeLE d s.2 (ocs_unitEdge d 1 (le_refl 1) p)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {s : ℕ // 1 ≤ s}) = ⟨Nat.sqrt n, hR⟩ from
      Subtype.ext hrr)

/-- The wired rotation residue at tilt `t` for the box pair `e'`: every lattice edge of every box
has the wired `q = 2` density of `e'` at `p = logistic t`. -/
def ocs_WiredRotationResidue (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) : Prop :=
  ∀ (m : ℕ) (eb : Sym2 (boxVerts d m)), eb ∈ (boxGraph d m).edgeFinset →
    wiredEdgeDensity d 2 (edgeIncl d m eb) (fsc_logistic t)
      = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)

/-- The wired marginal at `p = logistic t` of the unit edge `(j, sign)` in `Λ_{⌊√n⌋}`, and `0`
when `⌊√n⌋ = 0`. -/
noncomputable def ocs_unitWiredMarg (d n : ℕ) (p : Fin d × Bool) (t : ℝ) : ℝ :=
  if hR : 1 ≤ Nat.sqrt n then
    edgeMargProb
      (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n)) (fsc_logistic t) 2)
      (ocs_unitEdge d (Nat.sqrt n) hR p)
  else 0

/-- The total deviation of the wired unit-edge marginals in `Λ_{⌊√n⌋}` from the wired density of
`e'`. -/
noncomputable def ocs_wiredDelta (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ p : Fin d × Bool,
    |ocs_unitWiredMarg d n p t - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)|

lemma ocs_wiredDelta_nonneg (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) :
    0 ≤ ocs_wiredDelta N e' t n :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma ocs_wired_perDir_tendsto_zero (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_WiredRotationResidue (d := d) N e' t) (p : Fin d × Bool) :
    Tendsto (fun n => |ocs_unitWiredMarg d n p t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)|) atTop (𝓝 0) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hconv := ocs_unitEdge_wired_marg_tendsto d p hp hp1
  have hLeq : wiredEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) (fsc_logistic t)
      = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
    hres 1 (ocs_unitEdge d 1 (le_refl 1) p) (ocs_unitEdge1_mem_edgeFinset d p)
  rw [hLeq] at hconv
  have hmt : Tendsto (fun n => ocs_unitWiredMarg d n p t) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t))) := hconv.congr (fun n => rfl)
  have hsub := hmt.sub (tendsto_const_nhds
    (x := wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))
  rw [sub_self] at hsub
  have := hsub.abs
  rwa [abs_zero] at this

lemma ocs_wiredDelta_tendsto_zero (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hres : ocs_WiredRotationResidue (d := d) N e' t) :
    Tendsto (fun n => ocs_wiredDelta N e' t n) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ p : Fin d × Bool,
      |ocs_unitWiredMarg d n p t - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)|)
      atTop (𝓝 (∑ p : Fin d × Bool, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun p _ => ocs_wired_perDir_tendsto_zero N e' t hres p)
  rw [Finset.sum_const_zero] at h
  exact h

/-- The wired bulk edges of `Λ_n`: the edges of the inner box `Λ_{n - ⌊√n⌋ - 1}`. -/
noncomputable def ocs_wiredBulkSet (d n : ℕ) : Finset (Sym2 (boxVerts d n)) :=
  (boxGraph d (n - Nat.sqrt n - 1)).edgeFinset.image
    (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))))

/-- Every wired bulk edge of `Λ_n` has wired marginal at most `density(e') + ocs_wiredDelta`. -/
lemma ocs_wired_bulk_upper (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n - 1)) (hadj : (boxGraph d (n - Nat.sqrt n - 1)).Adj u v) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2)
        (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
          (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n - 1))))
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + ocs_wiredDelta N e' t n := by
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  have hRn1 : Nat.sqrt n + 1 ≤ n := by
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := by
      have := Nat.sqrt_le' n
      calc Nat.sqrt n * Nat.sqrt n = (Nat.sqrt n) ^ 2 := by ring
        _ ≤ n := this
    nlinarith [Nat.sqrt_le_self n, h2]
  have hmn : n - Nat.sqrt n - 1 ≤ n :=
    Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))
  obtain ⟨p0, hp0⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n - 1) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hp0]; exact ocs_candMap_mem_box d (Nat.sqrt n) hR p0
  have hup := ocs_wired_offCentre_upper d (Nat.sqrt n) n hR hRn1 hmn u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
        (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n))))
      = ocs_unitEdge d (Nat.sqrt n) hR p0 := by
    unfold ocs_unitEdge; congr 1; exact Subtype.ext hp0
  rw [hue] at hup
  have hmarg : ocs_unitWiredMarg d n p0 t
      = edgeMargProb (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n))
          (fsc_logistic t) 2) (ocs_unitEdge d (Nat.sqrt n) hR p0) := by
    unfold ocs_unitWiredMarg; rw [dite_eq_left hR]
  have hterm : |ocs_unitWiredMarg d n p0 t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ ocs_wiredDelta N e' t n :=
    Finset.single_le_sum
      (f := fun p => |ocs_unitWiredMarg d n p t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ p0)
  have h1 : ocs_unitWiredMarg d n p0 t
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + ocs_wiredDelta N e' t n := by
    have h2 : ocs_unitWiredMarg d n p0 t
        - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ ocs_wiredDelta N e' t n :=
      le_trans (le_abs_self _) hterm
    linarith
  rw [hmarg] at h1
  exact le_trans hup h1

/-- The wired off-centre sandwich from the wired rotation residues for all pairs `e'` of
`Λ_N`. -/
lemma ocs_wiredOffCentreSandwich_of_rotation (hd : 1 ≤ d) (N : ℕ)
    (hres : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    bdp_WiredOffCentreSandwich (d := d) N := by
  intro e' t
  refine ⟨ocs_wiredBulkSet d, ocs_wiredDelta N e' t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => ocs_wiredDelta_nonneg N e' t n
  · exact ocs_wiredDelta_tendsto_zero N e' t (hres e' t)
  · intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [edgeIncl_innerEdgeLE]
    exact hres e' t (n - Nat.sqrt n - 1) eb heb
  · intro n e he
    rw [ocs_wiredBulkSet, Finset.mem_image] at he
    obtain ⟨eb, heb, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at heb
    by_cases hn : 2 ≤ n
    · induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        exact ocs_wired_bulk_upper N e' t n hn u v heb
    · exfalso
      have hzero : n - Nat.sqrt n - 1 = 0 := by
        have hsq : Nat.sqrt n = 0 ∨ Nat.sqrt n = 1 := by
          interval_cases n <;> simp [Nat.sqrt]
        rcases hsq with h | h <;> rw [h] <;> omega
      induction eb with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet] at heb
        have huv : (u : Site d) = (v : Site d) := by
          have hu := u.2; have hv := v.2
          funext i
          have h1 := hu i; have h2 := hv i
          simp only [hzero] at h1 h2; omega
        rw [boxGraph, SimpleGraph.comap_adj] at heb
        change NearestNeighbour d (u : Site d) (v : Site d) at heb
        rw [huv] at heb
        rw [show NearestNeighbour d (v : Site d) (v : Site d)
              ↔ (∑ i, ((v : Site d) i - (v : Site d) i).natAbs) = 1 from Iff.rfl] at heb
        simp at heb
  · have hcard : ∀ n, (ocs_wiredBulkSet d n).card
        = (boxGraph d (n - Nat.sqrt n - 1)).edgeFinset.card :=
      fun n => Finset.card_image_of_injective _ (dfi_innerEdgeLE_injective d _)
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd (fun n => n - Nat.sqrt n - 1)
      (fun n => Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
      ocs_gap_sub_one_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]

end FK

end StatMech
