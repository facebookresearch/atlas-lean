/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Boundary forests for contracted-lattice trifurcations

Forest data with boundary leaves for contracted-lattice trifurcations bound the coarse count and,
for every configuration, exclude `N = ∞`.

## i. Overview

`bc68_GnForestData ω L R` is a finite forest without isolated vertices in which the
contracted-lattice trifurcations of `B_R` are branch vertices and whose leaves map injectively to
the boundary. Distinct arms of one trifurcation reach distinct boundary sites, and the branch–leaf
inequality gives the coarse counting bound. Two trifurcations can share a boundary site, so the
injectivity of leaves is a genuine condition; `bc60_upperLines` illustrates both facts.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc68_Gn_singleTrif_distinct_leaves` : one trifurcation reaches three distinct boundary sites
- `bc68_coarseTcount_le_boundary_of_GnForestData` : the coarse counting bound
- `bc68_multiTrif_shared_boundary_survives` : two trifurcations can share boundary sites
- `bc68_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

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

/-! ## A. Results -/

lemma bc68_no_shared_target (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b z : Site d)
    (hcut : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a b)
    (haz : (bc67_contractedLattice ω L y).Reachable a z)
    (hbz : (bc67_contractedLattice ω L y).Reachable b z) : False := by
  have haz' : Connected d (removeSites (bc61_boxAround d L y) ω) a z :=
    (bc67_Gn_deletion_eq_removeSites ω L y a z).mp haz
  have hbz' : Connected d (removeSites (bc61_boxAround d L y) ω) b z :=
    (bc67_Gn_deletion_eq_removeSites ω L y b z).mp hbz
  exact hcut (haz'.trans hbz'.symm)

lemma bc68_Gn_singleTrif_distinct_leaves (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (a : Fin 3 → Site d)
    (hcut01 : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 1))
    (hcut02 : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 2))
    (hcut12 : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 1) (a 2))
    (z : Fin 3 → Site d)
    (hreach : ∀ i, (bc67_contractedLattice ω L y).Reachable (a i) (z i)) :
    Function.Injective z := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; exact bc68_no_shared_target ω L y (a 0) (a 1) (z 0)
          hcut01 (hreach 0) (hij ▸ hreach 1))
      | (exfalso; exact bc68_no_shared_target ω L y (a 0) (a 2) (z 0)
          hcut02 (hreach 0) (hij ▸ hreach 2))
      | (exfalso; exact bc68_no_shared_target ω L y (a 1) (a 2) (z 1)
          hcut12 (hreach 1) (hij ▸ hreach 2))

lemma bc68_upperLines_boundaryPt {R : ℕ} (hR : 1 ≤ R) {h : ℤ} (hh : 1 ≤ h) (hhR : h ≤ (R : ℤ) - 1) :
    bc57_pt (R : ℤ) h ∈ vertexBoundary 2 R := by
  rw [vertexBoundary, Set.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [mem_box]; intro i; fin_cases i
    · change ((bc57_pt (R : ℤ) h) 0).natAbs ≤ R; rw [bc57_pt_fst]; simp
    · change ((bc57_pt (R : ℤ) h) 1).natAbs ≤ R; rw [bc57_pt_snd]; omega
  · rw [mem_box]; simp only [not_forall, not_le]
    refine ⟨0, ?_⟩
    have hcoord : ((bc57_pt (R : ℤ) h) 0).natAbs = R := by
      rw [bc57_pt_fst]; exact Int.natAbs_natCast R
    rw [hcoord]; omega

lemma bc68_upperLines_arm_reaches_R {L R : ℕ} (hLR : L + 1 ≤ R) {h : ℤ} (hh : 1 ≤ h) :
    Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h) (bc57_pt (R : ℤ) h) := by
  have hj := bc61_upperLines_rightArm_reach (L := L) hh (R - (L + 1))
  have hcast : ((L : ℤ) + 1 + ((R - (L + 1) : ℕ) : ℤ)) = (R : ℤ) := by
    have : ((R - (L + 1) : ℕ) : ℤ) = (R : ℤ) - ((L : ℤ) + 1) := by
      rw [Nat.cast_sub hLR]; push_cast; ring
    rw [this]; ring
  rwa [hcast] at hj

lemma bc68_upperLines_arms_reach_distinct {L R : ℕ} (hLR : L + 1 ≤ R) (hR3 : 4 ≤ R) :
    (∀ i : Fin 3,
      (bc67_contractedLattice bc60_upperLines L (0 : Site 2)).Reachable
        (bc57_pt ((L : ℤ) + 1) ((i : ℤ) + 1)) (bc57_pt (R : ℤ) ((i : ℤ) + 1)) ∧
      bc57_pt (R : ℤ) ((i : ℤ) + 1) ∈ vertexBoundary 2 R) ∧
    Function.Injective (fun i : Fin 3 => bc57_pt (R : ℤ) ((i : ℤ) + 1)) := by
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · rw [bc67_Gn_deletion_eq_removeSites]
      exact bc68_upperLines_arm_reaches_R hLR (by fin_cases i <;> norm_num)
    · exact bc68_upperLines_boundaryPt (by omega) (by fin_cases i <;> norm_num)
        (by fin_cases i <;> omega)
  · intro i j hij
    have : ((i : ℤ) + 1) = ((j : ℤ) + 1) := by
      have := congrArg (fun p => p 1) hij
      simpa [bc57_pt_snd] using this
    have hijZ : (i : ℤ) = (j : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast hijZ)

/-- Forest data for box size `L` and box `B_R`: a finite forest without isolated vertices with the
contracted-lattice trifurcations of `B_R` as branch vertices and leaves mapped injectively to
the boundary of `B_R`. -/
def bc68_GnForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : Nonempty W) (_ : DecidableEq W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj) (ιU : Site d → W) (lamL : W → Site d),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))

lemma bc68_connectedForest_of_GnForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc68_GnForestData ω L R) : bc65_ConnectedCoarseForest ω L R := by
  obtain ⟨W, _, _, _, G, _, ιU, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  exact bc67_Gn_armForest_of_forestData ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

lemma bc68_coarseTcount_le_boundary_of_GnForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc68_GnForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc65_coarseTcount_le_boundary_of_connectedForest ω L R
    (bc68_connectedForest_of_GnForestData ω L R h)

lemma bc68_infiniteClusters_top_null_of_GnForestData
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGnData : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc68_GnForestData ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc67_infiniteClusters_top_null_of_GnForest_route μ hd hinv hfe L
    (fun ω R => bc68_connectedForest_of_GnForestData ω L R (hGnData ω R)) hcoarseRoute

lemma bc68_multiTrif_shared_boundary_survives (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc66_shared_boundary_survives L

/-! ## B. Summary -/

lemma bc68_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (a : Fin 3 → Site d)
      (z : Fin 3 → Site d),
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 1) →
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 2) →
      ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 1) (a 2) →
      (∀ i, (bc67_contractedLattice ω L y).Reachable (a i) (z i)) →
      Function.Injective z) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc68_GnForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y a z h01 h02 h12 hreach
    exact bc68_Gn_singleTrif_distinct_leaves ω L y a h01 h02 h12 z hreach
  · intro ω L R h
    exact bc68_coarseTcount_le_boundary_of_GnForestData ω L R h
  · intro L
    exact bc68_multiTrif_shared_boundary_survives L

end StatMech.Walls
