/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonTrifProb
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryVolumeRatio

/-!
# Burton–Keane uniqueness from canonical trifurcations

Canonical trifurcations have probability zero for every translation-invariant measure in `d ≥ 1`;
with the canonical trifurcation step, ergodicity and finite energy give uniqueness of the infinite
cluster.

## i. Overview

The boundary of the box of radius `n + 1` is negligible relative to the box of radius `n`. The
canonical count `ctc2_canonTcount` is at most the boundary of the next box for every configuration,
so the expected canonical count gives `P(canonical trifurcation at 0) = 0` for every
translation-invariant measure (`cbk_canonical_trif_prob_eq_zero`). With the canonical trifurcation
step `0 < μ(N = ⊤) → 0 < μ(canonical trifurcation at 0)`, `N ≠ ⊤` almost surely, and the merge
argument gives the Burton–Keane conclusion (`cbk_canonical_uniqueness`).

**Fidelity.** `cbk_canonical_uniqueness` is conditional on the canonical trifurcation step `htrif`;
the probability-zero step and the counting are proved with no further hypothesis.

## ii. Key results

- `cbk_canonical_trif_prob_eq_zero` : canonical trifurcations have probability zero.
- `cbk_canonical_uniqueness` : uniqueness from the canonical trifurcation step.

## iii. Table of contents

- A. The boundary of the next box
- B. Uniqueness

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

namespace StatMech.Percolation

open StatMech StatMech.ConfigSpace MeasureTheory SimpleGraph Finset Filter Topology
open StatMech.Lattice
open scoped ENNReal

variable {d : ℕ}

/-! ## A. The boundary of the next box -/

/-- Same statement as `bc54_boundary_succ_vol_tendsto`; kept because `CoarseBoundaryTrifCount` is
not
imported by all its users. -/
lemma cbk_boundary_succ_vol_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ))
      atTop (𝓝 0) := by
  have hub : Tendsto (fun n : ℕ => (2 * (d : ℝ) * 3 ^ d) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (2 * (d : ℝ) * 3 ^ d))).div_atTop hden
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hub
  filter_upwards with n
  have hVn : ((boxFinsetBK d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
    unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  have hVn1 : ((boxFinsetBK d (n + 1)).card : ℝ) = (2 * (n : ℝ) + 3) ^ d := by
    unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  have hVnpos : (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := by rw [hVn]; positivity
  have hVn1pos : (0 : ℝ) < ((boxFinsetBK d (n + 1)).card : ℝ) := by rw [hVn1]; positivity
  have hr : (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d (n + 1)).card : ℝ)
      ≤ 2 * (d : ℝ) / ((n : ℝ) + 1) := by
    have h := bkc_boundary_vol_ratio_le d (n + 1) hd (Nat.le_add_left 1 n)
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hVratio : ((boxFinsetBK d (n + 1)).card : ℝ) ≤ 3 ^ d * ((boxFinsetBK d n).card : ℝ) := by
    rw [hVn1, hVn, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hAle : (boxSV_boundaryCard d (n + 1) : ℝ)
      ≤ (2 * (d : ℝ) * 3 ^ d / ((n : ℝ) + 1)) * ((boxFinsetBK d n).card : ℝ) := by
    have h1 : (boxSV_boundaryCard d (n + 1) : ℝ)
        ≤ (2 * (d : ℝ) / ((n : ℝ) + 1)) * ((boxFinsetBK d (n + 1)).card : ℝ) :=
      (div_le_iff₀ hVn1pos).mp hr
    have h2 : (2 * (d : ℝ) / ((n : ℝ) + 1)) * ((boxFinsetBK d (n + 1)).card : ℝ)
        ≤ (2 * (d : ℝ) / ((n : ℝ) + 1)) * (3 ^ d * ((boxFinsetBK d n).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hVratio (by positivity)
    calc (boxSV_boundaryCard d (n + 1) : ℝ) ≤ _ := h1
      _ ≤ _ := h2
      _ = (2 * (d : ℝ) * 3 ^ d / ((n : ℝ) + 1)) * ((boxFinsetBK d n).card : ℝ) := by ring
  rw [div_le_iff₀ hVnpos]
  exact hAle

/-! ## B. Uniqueness -/

lemma cbk_canonical_trif_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    μ {ω | IsCanonicalTrifurcation d ω 0} = 0 :=
  ctp_canonical_trifurcation_prob_eq_zero μ hinv (fun n => bkc_boxFinsetBK_card_pos d n)
    (cbk_boundary_succ_vol_tendsto d hd)

lemma cbk_numInfiniteClusters_ne_top (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  have htri0 : μ {ω | IsCanonicalTrifurcation d ω 0} = 0 :=
    cbk_canonical_trif_prob_eq_zero μ hd herg.isTranslationInvariant
  have htop0 : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
    by_contra h
    have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr h
    have := htrif hpos
    rw [htri0] at this
    exact (lt_irrefl 0) this
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  refine ⟨k, ?_, hk⟩
  intro hktop
  rw [hktop] at hk
  rw [hk] at htop0
  exact one_ne_zero htop0

/-- **Burton–Keane uniqueness via canonical trifurcations.** For an ergodic measure with finite
energy
for merges in `d ≥ 1`, if infinitely many infinite clusters with positive probability give a
canonical trifurcation at the origin with positive probability, then a.s. `N ∈ {0, 1}`. Burton and
Keane, *Density and uniqueness in percolation* (1989). -/
lemma cbk_canonical_uniqueness (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk
    obtain ⟨k', hk'top, hk'⟩ := cbk_numInfiniteClusters_ne_top μ hd herg htrif
    intro hktop
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hω]
      intro h; exact hk'top (by rw [← h, hktop])
    have hmk' : MeasurableSet
        {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
          = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
      rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
    have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
      le_antisymm prob_le_one (hk ▸ measure_mono hsub)
    have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
      (prob_compl_eq_one_iff hmk').mp hfull
    rw [hk'] at hnull
    exact one_ne_zero hnull
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top
      (fun k hk2 hktop hk => hmergeGeom_discharged μ k hk2 hktop hk)
  refine ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩

end StatMech.Percolation
