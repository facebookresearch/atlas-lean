/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnCoarseInfiniteCluster
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseMergeDichotomy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointBoxes

/-!
# Contracted-lattice trifurcations versus coarse trifurcations

The contracted-lattice trifurcation count equals the coarse count, and a coarse forest bounds it;
`bc60_upperLines` shows the coarse count can be positive with `N = ∞`.

## i. Overview

`bc83_genuineTrif` is the contracted-lattice trifurcation `bc67_IsGnTrifurcation`; its count
coincides with `bc61_coarseTcount`. A coarse forest leaf count bounds it by the boundary, and
translation invariance turns this into a null origin event and uniqueness for Bernoulli percolation.
In `bc60_upperLines` the origin is a contracted-lattice trifurcation and `N = ∞`, so the notion
counts configurations that a uniqueness argument must exclude.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc83_genuineTrif_iff_coarse` : the contracted-lattice and coarse notions agree
- `bc83_genuine_count_le_boundary_of_forest` : a coarse forest bounds the count
- `bc83_bk_from_forest` : uniqueness for Bernoulli percolation from a coarse forest for every
  configuration
- `bc83_status` : the statements together

## iii. Table of contents

- A. Definitions
- B. Results
- C. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The contracted-lattice trifurcation at `y` for box size `L`. -/
def bc83_genuineTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  bc67_IsGnTrifurcation ω L y

/-! ## B. Results -/

lemma bc83_genuineTrif_iff_coarse (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc83_genuineTrif ω L y ↔ bc61_IsCoarseTrifurcation ω L y :=
  (bc67_coarseTrif_is_G_n_trifurcation ω L y).symm

/-- The contracted-lattice trifurcations in `B_R`. -/
noncomputable def bc83_genuineTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => bc83_genuineTrif ω L y)

/-- The number of contracted-lattice trifurcations in `B_R`. -/
noncomputable def bc83_genuineTrifCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : ℕ :=
  (bc83_genuineTrifFinset ω L R).card

lemma bc83_genuineTrifFinset_eq_coarse (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc83_genuineTrifFinset ω L R = bc61_coarseTrifFinset ω L R := by
  classical
  ext y
  rw [bc83_genuineTrifFinset, Finset.mem_filter, bc61_mem_coarseTrifFinset,
    boxFinsetBK, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hy, hgen⟩; exact ⟨hy, (bc83_genuineTrif_iff_coarse ω L y).mp hgen⟩
  · rintro ⟨hy, hco⟩; exact ⟨hy, (bc83_genuineTrif_iff_coarse ω L y).mpr hco⟩

lemma bc83_no_overcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc83_genuineTrifCount ω L R = bc61_coarseTcount ω L R := by
  rw [bc83_genuineTrifCount, bc61_coarseTcount, bc83_genuineTrifFinset_eq_coarse]

lemma bc83_genuine_count_le_boundary_of_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_CoarseForestLeafCount ω L R) :
    bc83_genuineTrifCount ω L R ≤ boxSV_boundaryCard d R := by
  rw [bc83_no_overcount]
  exact bc61_coarseTcount_le_boundary_of_forest ω L R h

lemma bc83_expected (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L R : ℕ) :
    ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc83_genuineTrif ω L 0}
      = ∫⁻ ω, (bc83_genuineTrifCount ω L R : ℝ≥0∞) ∂μ := by
  have hset : {ω : ConfigSpace (Sym2 (Site d)) | bc83_genuineTrif ω L 0}
      = {ω | bc61_IsCoarseTrifurcation ω L 0} := by
    ext ω; exact bc83_genuineTrif_iff_coarse ω L 0
  have hcount : ∀ ω : ConfigSpace (Sym2 (Site d)),
      bc83_genuineTrifCount ω L R = bc61_coarseTcount ω L R :=
    fun ω => bc83_no_overcount ω L R
  rw [hset]
  simp_rw [hcount]
  exact bc62_coarse_expectation μ hinv L R

lemma bc83_prob_zero (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R) :
    μ {ω | bc83_genuineTrif ω L 0} = 0 := by
  have hset : {ω : ConfigSpace (Sym2 (Site d)) | bc83_genuineTrif ω L 0}
      = {ω | bc61_IsCoarseTrifurcation ω L 0} := by
    ext ω; exact bc83_genuineTrif_iff_coarse ω L 0
  rw [hset]
  exact bc73_coarseTrif_prob_eq_zero_of_sublatticeForest μ hd L
    (fun R => bc62_coarse_expectation μ hinv L R) hforest

lemma bc83_bk_from_genuine (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc83_genuineTrif ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have hset : {ω : ConfigSpace (Sym2 (Site d)) | bc83_genuineTrif ω L 0}
      = {ω | bc61_IsCoarseTrifurcation ω L 0} := by
    ext ω; exact bc83_genuineTrif_iff_coarse ω L 0
  rw [hset] at h0
  exact bc78_bk_closed μ hd L hinv h0 hexist

lemma bc83_bk_from_forest (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc83_bk_from_genuine μ hd L hinv (bc83_prob_zero μ hd L hinv hforest) hexist

lemma bc83_upperLines_genuineTrif_at_zero {L : ℕ} (hL : 3 ≤ L) :
    bc83_genuineTrif bc60_upperLines L (0 : Site 2) :=
  bc67_upperLines_is_G_n_trifurcation hL

lemma bc83_upperLines_overcount_note {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
      bc83_genuineTrif bc60_upperLines L (0 : Site 2) :=
  ⟨bc61_wholeBox_severs_upperLines hL, bc83_upperLines_genuineTrif_at_zero hL⟩

/-! ## C. Summary -/

lemma bc83_status :
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bc83_genuineTrifCount ω L R = bc61_coarseTcount ω L R) ∧
    (∀ (W : Type) (_ : Fintype W) (_ : Nonempty W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bc61_CoarseForestLeafCount ω L R → bc83_genuineTrifCount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      μ {ω | bc83_genuineTrif ω L 0} = 0 → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    (∀ {L : ℕ}, 3 ≤ L → bc83_genuineTrif bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R; exact bc83_no_overcount ω L R
  · intro W _ _ G _ hacyc hmin; exact StatMech.Percolation.flc2_forest_internal_le_leaves G hacyc hmin
  · intro ω L R h; exact bc83_genuine_count_le_boundary_of_forest ω L R h
  · intro μ _ L hinv h0 hexist; exact bc83_bk_from_genuine μ (by norm_num) L hinv h0 hexist
  · intro L hL; exact bc83_upperLines_genuineTrif_at_zero hL

end StatMech.Walls
