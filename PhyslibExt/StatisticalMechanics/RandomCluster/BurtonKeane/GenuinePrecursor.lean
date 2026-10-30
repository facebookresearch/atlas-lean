/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleSiteRewiring

/-!
# Single-site precursors of classical trifurcations

Opening three edges at the origin turns a single-site precursor into a classical trifurcation;
classical trifurcations split into interior and boundary ones.

## i. Overview

A single-site precursor at the origin consists of three neighbours `a_i` connected, after the origin
is removed, to sites `x_i` in three distinct infinite clusters. Forcing the three edges `0 a_i` open
makes the origin a classical trifurcation (`bc97_forceOrigin_genuineTrif`). The classical
trifurcations of `B_n` split into those in `B_{n-1}` and those on the boundary layer, and the latter
number at most `|∂B_n|`.

## ii. Key results

- `bc97_forceOrigin_genuineTrif` : forcing three edges at the origin creates a classical
  trifurcation
- `bc97_precursor_subset_force_genuineTrif` : the precursor event maps into the trifurcation event
- `bc97_genuineCount_le_interior_plus_boundary` : interior plus boundary decomposition of the count
- `bc97_status` : the statements together

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
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The classical trifurcations of `B_n` that lie outside `B_{n-1}`. -/
noncomputable def bc97_boundaryGenuineFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) := by
  classical
  exact (bc89_genuineTrifFinset ω n).filter (fun x => x ∉ box d (n - 1))

/-- The classical trifurcations of `B_n` that lie in `B_{n-1}`. -/
noncomputable def bc97_interiorGenuineFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) := by
  classical
  exact (bc89_genuineTrifFinset ω n).filter (fun x => x ∈ box d (n - 1))

/-! ## B. Results -/

lemma bc97_boundaryGenuine_subset_vertexBoundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc97_boundaryGenuineFinset ω n ⊆ (vertexBoundary_finite d n).toFinset := by
  classical
  intro x hx
  rw [bc97_boundaryGenuineFinset, Finset.mem_filter] at hx
  obtain ⟨hxgen, hxnint⟩ := hx
  rw [bc89_genuineTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset] at hxgen
  rw [Set.Finite.mem_toFinset, mem_vertexBoundary]
  exact ⟨hxgen.1, hxnint⟩

lemma bc97_boundary_genuineCount_le (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc97_boundaryGenuineFinset ω n).card ≤ boxSV_boundaryCard d n := by
  classical
  unfold boxSV_boundaryCard
  exact Finset.card_le_card (bc97_boundaryGenuine_subset_vertexBoundary ω n)

lemma bc97_genuineCount_split (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc89_genuineTcount ω n
      = (bc97_interiorGenuineFinset ω n).card + (bc97_boundaryGenuineFinset ω n).card := by
  classical
  unfold bc89_genuineTcount bc97_interiorGenuineFinset bc97_boundaryGenuineFinset
  exact (Finset.card_filter_add_card_filter_not
    (s := bc89_genuineTrifFinset ω n) (p := fun x => x ∈ box d (n - 1))).symm

lemma bc97_genuineCount_le_interior_plus_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc89_genuineTcount ω n
      ≤ (bc97_interiorGenuineFinset ω n).card + boxSV_boundaryCard d n := by
  rw [bc97_genuineCount_split ω n]
  exact Nat.add_le_add_left (bc97_boundary_genuineCount_le ω n) _

lemma bc97_forceOrigin_genuineTrif (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ x₁ x₂ x₃ : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧
      Connected d (removeSite 0 ω) a₃ x₃)
    (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) :
    bc89_GenuineTrif d (forceOpenFinset {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} ω) 0 := by
  classical
  set F : Finset (Sym2 (Site d)) := {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} with hFdef
  set ω' := forceOpenFinset F ω with hω'
  obtain ⟨hadj1, hadj2, hadj3⟩ := hadj
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> · rw [h]; exact Sym2.mem_mk_left _ _
  have hrm : removeSite 0 ω' = removeSite 0 ω := removeSite_forceOpen_eq 0 F hFmem ω
  have ho1 : ω' s(0, a₁) = true := forceOpenFinset_of_mem (by simp [hFdef]) ω
  have ho2 : ω' s(0, a₂) = true := forceOpenFinset_of_mem (by simp [hFdef]) ω
  have ho3 : ω' s(0, a₃) = true := forceOpenFinset_of_mem (by simp [hFdef]) ω
  refine bc96_genuineTrif_of_reachOrigin_full ω' (x₁ := x₁) (x₂ := x₂) (x₃ := x₃)
    ⟨hadj1, hadj2, hadj3⟩ ?_ ?_ ?_ ⟨ho1, ho2, ho3⟩
  · rw [hrm]; exact hconn
  · rw [hrm]; exact hinf
  · rw [hrm]; exact hdist

/-- The single-site precursor event at the origin for neighbours `a_i` and targets `x_i`: after
removing the origin each `a_i` reaches `x_i`, whose clusters are infinite and pairwise distinct. -/
def bc97_SingleSitePrecursor (d : ℕ) (a₁ a₂ a₃ x₁ x₂ x₃ : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧
      Connected d (removeSite 0 ω) a₃ x₃) ∧
    ((cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∧
    (cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃)}

lemma bc97_precursor_subset_force_genuineTrif (a₁ a₂ a₃ x₁ x₂ x₃ : Site d) :
    bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ ⊆
      (fun ω => forceOpenFinset {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} ω)
        ⁻¹' {ω | bc89_GenuineTrif d ω 0} := by
  rintro ω ⟨hadj, hconn, hinf, hdist⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  exact bc97_forceOrigin_genuineTrif ω hadj hconn hinf hdist

lemma bc97_close_a (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hroute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d,
        0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃)) :
    bc95_SingleSiteRewiring μ := by
  refine bc96_singleSiteRewiring_of_precursor μ hfe ?_
  intro hpos
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hpre⟩ := hroute hpos
  exact ⟨{s((0 : Site d), a₁), s(0, a₂), s(0, a₃)}, _, hpre,
    bc97_precursor_subset_force_genuineTrif a₁ a₂ a₃ x₁ x₂ x₃⟩

lemma bc97_bk_from_route (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hroute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d,
        0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc95_bk_from_residues μ hprob0 (bc97_close_a μ hfe hroute)

lemma bc97_upperLines_boundary_count_zero (n : ℕ) :
    (bc97_boundaryGenuineFinset bc60_upperLines n).card = 0 ∧
    (bc97_interiorGenuineFinset bc60_upperLines n).card = 0 := by
  classical
  have h0 : bc89_genuineTrifFinset bc60_upperLines n = ∅ := by
    have := bc89_upperLines_genuineTcount_zero n
    rw [bc89_genuineTcount, Finset.card_eq_zero] at this
    exact this
  constructor
  · rw [bc97_boundaryGenuineFinset, h0, Finset.filter_empty, Finset.card_empty]
  · rw [bc97_interiorGenuineFinset, h0, Finset.filter_empty, Finset.card_empty]

/-! ## C. Summary -/

lemma bc97_status :
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2},
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) →
      (Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃) →
      ((cluster 2 (removeSite 0 ω) x₁).Infinite ∧ (cluster 2 (removeSite 0 ω) x₂).Infinite ∧
        (cluster 2 (removeSite 0 ω) x₃).Infinite) →
      (cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₂ ∧
        cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₃ ∧
        cluster 2 (removeSite 0 ω) x₂ ≠ cluster 2 (removeSite 0 ω) x₃) →
      bc89_GenuineTrif 2 (forceOpenFinset {s((0 : Site 2), a₁), s(0, a₂), s(0, a₃)} ω) 0) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ →
      (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2,
          0 < μ (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) →
      bc95_SingleSiteRewiring μ) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 →
      (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} →
        ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2,
          0 < μ (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
      (bc97_boundaryGenuineFinset ω n).card ≤ boxSV_boundaryCard 2 n) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
      bc89_genuineTcount ω n ≤ (bc97_interiorGenuineFinset ω n).card + boxSV_boundaryCard 2 n) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
        ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω a₁ a₂ a₃ x₁ x₂ x₃ hadj hconn hinf hdist
    exact bc97_forceOrigin_genuineTrif ω hadj hconn hinf hdist
  · intro μ _ hfe hroute; exact bc97_close_a μ hfe hroute
  · intro μ _ hfe hprob0 hroute; exact bc97_bk_from_route μ hfe hprob0 hroute
  · intro ω n; exact bc97_boundary_genuineCount_le ω n
  · intro ω n; exact bc97_genuineCount_le_interior_plus_boundary ω n
  · intro ω n hn hcanon harmbox; exact bc90_genuineTcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox

end StatMech.Walls
