/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxQuotient
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Sublattice fibres of coarse trifurcations

Coarse trifurcations with the same residue modulo `2L + 1` have disjoint boxes; a forest bound on
each fibre bounds the coarse count by a constant times the boundary, which excludes `N = ∞`.

## i. Overview

`bc73_resVec L y` is the residue of `y` modulo `2L + 1` coordinatewise, and `bc73_fiber ω L R c` the
coarse trifurcations of `B_R` with residue `c`. Boxes of distinct sites in a fibre are disjoint. If
every fibre has at most `|∂B_R|` elements (`bc73_SublatticeForest`), the coarse count is at most
`(2L + 1)^d |∂B_R|`, which is `o(|B_R|)`, so translation invariance forces the coarse trifurcation
probability to vanish and excludes `N = ∞`.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc73_sameResidue_boxes_disjoint` : same-residue boxes are disjoint
- `bc73_coarseTrif_prob_eq_zero_of_sublatticeForest` : fibre bounds force zero coarse trifurcation
  probability
- `bc73_infiniteClusters_top_null` : fibre bounds for every configuration exclude `N = ∞`
- `bc73_status` : the statements together

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

/-- `y` lies on the sublattice `(2L + 1)ℤ^d`. -/
def bc73_onSublattice (L : ℕ) (y : Site d) : Prop := ∀ i, ((2 * L + 1 : ℤ) ∣ y i)

/-- Membership in the sublattice is decidable. -/
instance (L : ℕ) (y : Site d) : Decidable (bc73_onSublattice L y) := by
  unfold bc73_onSublattice; infer_instance

/-! ## B. Results -/

lemma bc73_far_of_onSublattice {L : ℕ} {y y' : Site d}
    (hy : bc73_onSublattice L y) (hy' : bc73_onSublattice L y') (hne : y ≠ y') :
    ∃ i, 2 * L < ((y - y') i).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ y' i := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (funext h)
  refine ⟨i, ?_⟩
  have hdvd : (2 * L + 1 : ℤ) ∣ (y - y') i := by
    rw [Pi.sub_apply]; exact dvd_sub (hy i) (hy' i)
  have hnz : (y - y') i ≠ 0 := by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hi
  have hpos : (0 : ℤ) < 2 * L + 1 := by positivity
  have hge : (2 * L + 1 : ℤ) ≤ |(y - y') i| := by
    have hdvdabs : (2 * L + 1 : ℤ) ∣ |(y - y') i| := (dvd_abs _ _).mpr hdvd
    exact Int.le_of_dvd (abs_pos.mpr hnz) hdvdabs
  have hge' : (2 * L + 1 : ℤ) ≤ ((y - y') i).natAbs := by
    rwa [Int.abs_eq_natAbs] at hge
  have : (2 * L + 1 : ℕ) ≤ ((y - y') i).natAbs := by exact_mod_cast hge'
  omega

lemma bc73_sublattice_boxes_disjoint {L : ℕ} {y y' : Site d}
    (hy : bc73_onSublattice L y) (hy' : bc73_onSublattice L y') (hne : y ≠ y') :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') :=
  bc64_boxAround_disjoint_of_far (bc73_far_of_onSublattice hy hy' hne)

/-- The sublattice sites of `B_R`. -/
noncomputable def bc73_sublattice (d L R : ℕ) : Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => bc73_onSublattice L y)

lemma bc73_mem_sublattice {L R : ℕ} {y : Site d} :
    y ∈ bc73_sublattice d L R ↔ y ∈ box d R ∧ bc73_onSublattice L y := by
  classical
  rw [bc73_sublattice, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]

lemma bc73_sublattice_pairwise_disjoint (L R : ℕ) :
    (bc73_sublattice d L R : Set (Site d)).Pairwise
      (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
  intro y hy y' hy' hne
  rw [Finset.mem_coe, bc73_mem_sublattice] at hy hy'
  exact bc73_sublattice_boxes_disjoint hy.2 hy'.2 hne

/-- The coordinatewise residue of `y` modulo `2L + 1`. -/
def bc73_resVec (L : ℕ) (y : Site d) : Fin d → Fin (2 * L + 1) :=
  fun i => ⟨(y i % (2 * L + 1 : ℤ)).toNat, by
    have hpos : (0 : ℤ) < 2 * L + 1 := by positivity
    have h1 : 0 ≤ y i % (2 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
    have h2 : y i % (2 * L + 1 : ℤ) < 2 * L + 1 := Int.emod_lt_of_pos _ hpos
    omega⟩

lemma bc73_far_of_sameResidue {L : ℕ} {y y' : Site d}
    (hres : bc73_resVec L y = bc73_resVec L y') (hne : y ≠ y') :
    ∃ i, 2 * L < ((y - y') i).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ y' i := by
    by_contra h; simp only [not_exists, not_not] at h; exact hne (funext h)
  refine ⟨i, ?_⟩
  have hposZ : (0 : ℤ) < 2 * L + 1 := by positivity
  have hresi : (y i % (2 * L + 1 : ℤ)).toNat = (y' i % (2 * L + 1 : ℤ)).toNat := by
    have := congrArg (fun f => (f i).val) hres
    simpa [bc73_resVec] using this
  have hnn1 : 0 ≤ y i % (2 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hnn2 : 0 ≤ y' i % (2 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hemodeq : y i % (2 * L + 1 : ℤ) = y' i % (2 * L + 1 : ℤ) := by
    have : (y i % (2 * L + 1 : ℤ)).toNat = (y' i % (2 * L + 1 : ℤ)).toNat := hresi
    omega
  have hdvd : (2 * L + 1 : ℤ) ∣ (y - y') i := by
    rw [Pi.sub_apply]
    have hmodeq : (y i - y' i) % (2 * L + 1 : ℤ) = 0 := by
      rw [Int.sub_emod, hemodeq, sub_self, Int.zero_emod]
    exact Int.dvd_of_emod_eq_zero hmodeq
  have hnz : (y - y') i ≠ 0 := by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hi
  have hdvdabs : (2 * L + 1 : ℤ) ∣ |(y - y') i| := (dvd_abs _ _).mpr hdvd
  have hge : (2 * L + 1 : ℤ) ≤ |(y - y') i| := Int.le_of_dvd (abs_pos.mpr hnz) hdvdabs
  have hge' : (2 * L + 1 : ℤ) ≤ ((y - y') i).natAbs := by rwa [Int.abs_eq_natAbs] at hge
  have : (2 * L + 1 : ℕ) ≤ ((y - y') i).natAbs := by exact_mod_cast hge'
  omega

lemma bc73_sameResidue_boxes_disjoint {L : ℕ} {y y' : Site d}
    (hres : bc73_resVec L y = bc73_resVec L y') (hne : y ≠ y') :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') :=
  bc64_boxAround_disjoint_of_far (bc73_far_of_sameResidue hres hne)

/-- The coarse trifurcations of `B_R` with residue `c`. -/
noncomputable def bc73_fiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) : Finset (Site d) := by
  classical
  exact (bc61_coarseTrifFinset ω L R).filter (fun y => bc73_resVec L y = c)

lemma bc73_fiber_pairwise_disjoint (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    (bc73_fiber ω L R c : Set (Site d)).Pairwise
      (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
  classical
  intro y hy y' hy' hne
  rw [Finset.mem_coe, bc73_fiber, Finset.mem_filter] at hy hy'
  exact bc73_sameResidue_boxes_disjoint (hy.2.trans hy'.2.symm) hne

/-- Every residue fibre of coarse trifurcations of `B_R` has at most `|∂B_R|` elements. -/
def bc73_SublatticeForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∀ c : Fin d → Fin (2 * L + 1), (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R

lemma bc73_covering (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc73_SublatticeForest ω L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
  classical
  set f : Site d → (Fin d → Fin (2 * L + 1)) := bc73_resVec L with hf
  set t : Finset (Fin d → Fin (2 * L + 1)) := Finset.univ with ht
  have hmaps : ∀ y ∈ bc61_coarseTrifFinset ω L R, f y ∈ t := fun y _ => Finset.mem_univ _
  have hfib : ∀ c ∈ t, ({y ∈ bc61_coarseTrifFinset ω L R | f y = c}).card
      ≤ boxSV_boundaryCard d R := by
    intro c _
    have hval : ({y ∈ bc61_coarseTrifFinset ω L R | f y = c}) = bc73_fiber ω L R c := by
      rw [bc73_fiber]
    rw [hval]; exact h c
  have hcard : (bc61_coarseTrifFinset ω L R).card ≤ boxSV_boundaryCard d R * t.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps (boxSV_boundaryCard d R) hfib
  have htcard : t.card = (2 * L + 1) ^ d := by
    rw [ht, Finset.card_univ]
    rw [Fintype.card_pi]
    simp [Fintype.card_fin]
  rw [bc61_coarseTcount]
  calc (bc61_coarseTrifFinset ω L R).card ≤ boxSV_boundaryCard d R * t.card := hcard
    _ = boxSV_boundaryCard d R * (2 * L + 1) ^ d := by rw [htcard]
    _ = (2 * L + 1) ^ d * boxSV_boundaryCard d R := by ring

lemma bc73_const_boundary_vol_tendsto (d : ℕ) (hd : 1 ≤ d) (L : ℕ) :
    Tendsto (fun R => (((2 * L + 1) ^ d * boxSV_boundaryCard d R : ℕ) : ℝ)
        / ((boxFinsetBK d R).card : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun R => (boxSV_boundaryCard d R : ℝ) / ((boxFinsetBK d R).card : ℝ))
      atTop (𝓝 0) := bkc_boundary_vol_tendsto d hd
  have hconst : Tendsto
      (fun R => ((2 * L + 1) ^ d : ℝ)
        * ((boxSV_boundaryCard d R : ℝ) / ((boxFinsetBK d R).card : ℝ)))
      atTop (𝓝 ((2 * L + 1) ^ d * 0)) :=
    Filter.Tendsto.const_mul _ hbase
  rw [mul_zero] at hconst
  refine hconst.congr (fun R => ?_)
  push_cast
  rw [mul_div_assoc]

lemma bc73_coarseTrif_prob_eq_zero_of_sublatticeForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc61_coarseTrif_prob_eq_zero μ L (fun R => (2 * L + 1) ^ d * boxSV_boundaryCard d R)
    hexp
    (fun ω R => bc73_covering ω L R (hforest ω R))
    (fun R => bkc_boxFinsetBK_card_pos d R)
    (bc73_const_boundary_vol_tendsto d hd L)

lemma bc73_infiniteClusters_top_null
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc61_infiniteClusters_top_null_of_coarse μ L
    (fun R => (2 * L + 1) ^ d * boxSV_boundaryCard d R)
    hexp
    (fun ω R => bc73_covering ω L R (hforest ω R))
    (fun R => bkc_boxFinsetBK_card_pos d R)
    (bc73_const_boundary_vol_tendsto d hd L)
    hexist

lemma bc73_disjointBoxes_deg3 {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (h : bc67_IsGnTrifurcation ω L y) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ :=
  bc72_quot_deg3_of_gnTrif h

lemma bc73_fiber_empty_bound (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
  rw [hempty]; simp

lemma bc73_sublatticeForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hno : bc61_coarseTrifFinset ω L R = ∅) : bc73_SublatticeForest ω L R := by
  classical
  intro c
  have hfib : bc73_fiber ω L R c = ∅ := by
    rw [bc73_fiber, hno]; simp
  rw [hfib]; simp

lemma bc73_upperLines_sublattice_disjoint (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) :=
  bc64_disjointBoxes_multiTrif L

lemma bc73_upperLines_deg3_sublattice {L : ℕ} (hL : 3 ≤ L) :
    ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (hyS : (0 : Site 2) ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph 2 bc60_upperLines)
              (bc72_collapseBox L (0 : Site 2))).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph 2 bc60_upperLines)
            (bc72_collapseBox L (0 : Site 2))).induce S).degree ⟨0, hyS⟩ :=
  bc72_upperLines_deg3 hL

/-! ## C. Summary -/

lemma bc73_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      (bc73_fiber ω L R c : Set (Site d)).Pairwise
        (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y'))) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc73_SublatticeForest ω L R →
      bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R) ∧
    (1 ≤ d → ∀ L : ℕ,
      Tendsto (fun R => (((2 * L + 1) ^ d * boxSV_boundaryCard d R : ℕ) : ℝ)
          / ((boxFinsetBK d R).card : ℝ)) atTop (𝓝 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R c; exact bc73_fiber_pairwise_disjoint ω L R c
  · intro ω L R h; exact bc73_covering ω L R h
  · intro hd L; exact bc73_const_boundary_vol_tendsto d hd L

end StatMech.Walls
