/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestInsertionTolerance
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointStarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount

/-!
# Coarse counts in expectation

A bound on the expected coarse count of vanishing density gives probability zero for coarse
trifurcations; forests whose leaves inject into a set of size `m` bound the coarse count by `m`.

## i. Overview

If `|Λ_R| · P(coarse trifurcation at 0) ≤ bdry R` with `bdry R / |Λ_R| → 0`, the probability is zero
and, with the coarse step, `μ(N = ⊤) = 0`. `bpe_CoarseForestNoBnd ω L R m` asks for a finite forest
through the coarse trifurcations whose leaves inject into a set of size `m`; it bounds the coarse
count by `m`, and the full forest leaf count gives it with `m = |∂Λ_R|`. Per-configuration leaf
bounds give the expectation bound.

## ii. Key results

- `bpe_coarseTrif_prob_eq_zero_of_expBound` : probability zero from an expectation bound.
- `bpe_coarseTcount_le_leafCard` : the coarse count from a leaf injection.

## iii. Table of contents

- A. Expectation bounds
- B. Forests with a leaf bound

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Expectation bounds -/

lemma bpe_coarseTrif_prob_eq_zero_of_expBound
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hExpBound : ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞))
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | bc61_IsCoarseTrifurcation ω L 0} with hp
  have hkey : ∀ R, ((boxFinsetBK d R).card : ℝ≥0∞) * p ≤ (bdry R : ℝ≥0∞) := by
    intro R; rw [hexp R]; exact hExpBound R
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ R, ((boxFinsetBK d R).card : ℝ) * pr ≤ (bdry R : ℝ) := by
    intro R
    have h := hkey R
    have h' : (((boxFinsetBK d R).card : ℝ≥0∞) * p).toReal ≤ (bdry R : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ R, (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := fun R => by exact_mod_cast hvol R
  have hle : ∀ R, pr ≤ (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ) := by
    intro R
    rw [le_div_iff₀ (hvolr R)]
    linarith [hkeyr R]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this

lemma bpe_top_null_of_expCount
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hExpBound : ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞))
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have hprob0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
    bpe_coarseTrif_prob_eq_zero_of_expBound μ L bdry hexp hExpBound hvol hdens
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [hprob0] at this
  exact lt_irrefl 0 this

/-! ## B. Forests with a leaf bound -/

/-- A finite forest through the coarse trifurcations of the box, each of degree at least three,
whose
leaves inject into a set of `m` sites. -/
def bpe_CoarseForestNoBnd (ω : ConfigSpace (Sym2 (Site d))) (L R m : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : Nonempty W) (_ : DecidableEq W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj) (ιT : Site d → W),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y)) ∧
    (∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z) ∧
    (univ.filter (fun v => G.degree v = 1)).card ≤ m

lemma bpe_coarseTcount_le_leafCard (ω : ConfigSpace (Sym2 (Site d))) (L R m : ℕ)
    (h : bpe_CoarseForestNoBnd ω L R m) :
    bc61_coarseTcount ω L R ≤ m := by
  classical
  obtain ⟨W, _, _, _, G, _, ιT, hacyc, hmin, hdeg3, hιinj, hleaf⟩ := h
  set Tf := bc61_coarseTrifFinset ω L R with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  have hιinjOn : Set.InjOn ιT Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, bc61_mem_coarseTrifFinset] at hy hz
    exact hιinj y hy.1 hy.2 z hz.1 hz.2 hyz
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hyT, rfl⟩ := hw
    rw [bc61_mem_coarseTrifFinset] at hyT
    exact hdeg3 y hyT.1 hyT.2
  calc bc61_coarseTcount ω L R = Tf.card := rfl
    _ = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := flc2_trifImage_card_le_deg3 G Tw hTwdeg
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card :=
        flc2_forest_internal_le_leaves G hacyc hmin
    _ ≤ m := hleaf

lemma bpe_noBnd_of_fullForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_CoarseForestLeafCount ω L R) :
    bpe_CoarseForestNoBnd ω L R (boxSV_boundaryCard d R) := by
  classical
  obtain ⟨W, hWf, hWne, hWde, G, hGdr, ιT, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  refine ⟨W, hWf, hWne, hWde, G, hGdr, ιT, hacyc, hmin, hdeg3, hιinj, ?_⟩
  exact flc2_leaf_card_le_boundary G R lamL hlammap hlaminj

lemma bpe_expBound_of_perConfigLeaf
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ) (bdry : ℕ → ℕ)
    (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ)
    (hle : ∀ ω R, bc61_coarseTcount ω L R ≤ leafBd ω R)
    (hExp : ∀ R, ∫⁻ ω, (leafBd ω R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞)) :
    ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞) := by
  intro R
  refine le_trans (lintegral_mono (fun ω => ?_)) (hExp R)
  exact Nat.cast_le.mpr (hle ω R)

lemma bpe_top_null_of_probForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (_hd : 1 ≤ d) (L : ℕ)
    (bdry : ℕ → ℕ) (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
      bpe_CoarseForestNoBnd ω L R (leafBd ω R))
    (hExpLeaf : ∀ R, ∫⁻ ω, (leafBd ω R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞))
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have ha : ∀ ω R, bc61_coarseTcount ω L R ≤ leafBd ω R :=
    fun ω R => bpe_coarseTcount_le_leafCard ω L R (leafBd ω R) (hforest ω R)
  have hExpBound : ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞) :=
    bpe_expBound_of_perConfigLeaf μ L bdry leafBd ha hExpLeaf
  exact bpe_top_null_of_expCount μ L bdry
    (fun R => bc62_coarse_expectation μ hinv L R) hExpBound
    (fun R => bkc_boxFinsetBK_card_pos d R) hdens hexist

lemma bpe_status (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (hd : 1 ≤ d) (L : ℕ)
    (bdry : ℕ → ℕ) :
    ((∀ R : ℕ,
        ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
          = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) →
      (∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞)) →
      (∀ R, 0 < (boxFinsetBK d R).card) →
      Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (R m : ℕ),
      bpe_CoarseForestNoBnd ω L R m → bc61_coarseTcount ω L R ≤ m) ∧
    (∀ (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ),
      (∀ ω R, bpe_CoarseForestNoBnd ω L R (leafBd ω R)) →
      (∀ R, ∫⁻ ω, (leafBd ω R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞)) →
      Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hexp hExpBound hvol hdens hexist
    exact bpe_top_null_of_expCount μ L bdry hexp hExpBound hvol hdens hexist
  · intro ω R m h; exact bpe_coarseTcount_le_leafCard ω L R m h
  · intro leafBd hforest hExpLeaf hdens hexist
    exact bpe_top_null_of_probForest μ hinv hd L bdry leafBd hforest hExpLeaf hdens hexist

end StatMech.Walls
