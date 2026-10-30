/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedPathChain
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCutUnbounded
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForceMonotone
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorRayDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses

/-!
# Forced corridor routing

Three axis corridors whose forced versions keep the mouths pairwise separated give distinct-cluster
corridors and corridor covers; neighbour witnesses with separated cut clusters give such routing.

## i. Overview

Forcing the corridor along `j` of length `L + 1` gives a chain of corridor steps from the mouth to
the far end. `bc2_PairwiseSeparated` asks the three mouths to stay disconnected after forcing all
three corridors. `bc2_ForcedCorridorRouting ω` asks for three distinct axes and lengths with
infinite cut clusters at the far ends and separated mouths. It gives distinct-cluster corridors, and
its box version `bc2_BoxForcedCorridorRouting` gives corridor covers of `threeMeetBox`. Neighbour
witnesses with separated cut clusters give it with lengths `0`.

**Fidelity.** `bc2_burtonKeane_uniqueness_of_box` also assumes the counting hypotheses of
`burton_keane_uniqueness_full`, which are unsatisfiable for `d ≥ 1` (`tfc_not_hbound_hdens`), so it
has content only for `d = 0`.

## ii. Key results

- `bc2_csc_of_forcedCorridorRouting` : distinct-cluster corridors from forced routing.
- `bc2_corridorCover_of_box` : corridor covers from the box version.

## iii. Table of contents

- A. Forced corridors
- B. Forced routing
- C. Neighbour witnesses

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Forced corridors -/

lemma bc2_corridorChain_in_union (j : Fin d) (L : ℕ) (G : Finset (Sym2 (Site d)))
    (hsub : hrHD_corridorEdges j (L + 1) ⊆ G) :
    Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
  have hchain := bc2_corridorChain j L (L + 1) (by omega) le_rfl
  have he : (((L + 1 : ℕ) : ℤ)) = ((L : ℤ) + 1) := by push_cast; ring
  rw [he] at hchain
  exact Relation.ReflTransGen.mono (fun u v hstep => ⟨hstep.1, hsub hstep.2.1, hstep.2.2⟩) _ _
    hchain

/-- After forcing the three corridors and removing the origin, the three mouths are pairwise
disconnected. -/
def bc2_PairwiseSeparated (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) : Prop :=
  ¬ Connected d (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧
    ¬ Connected d (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧
    ¬ Connected d (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ω)) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)

/-! ## B. Forced routing -/

/-- Forced corridor routing: three distinct axes and lengths such that the far ends have infinite
cut
clusters and the mouths are pairwise separated after forcing. -/
def bc2_ForcedCorridorRouting (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ),
    (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    ((cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite ∧
      (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite ∧
      (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite) ∧
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃

lemma bc2_csc_of_forcedCorridorRouting (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc2_ForcedCorridorRouting ω) : csc_DistinctClusterCorridors ω := by
  obtain ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩, hsep12, hsep13, hsep23⟩ := h
  set G : Finset (Sym2 (Site d)) :=
    hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
      hrHD_corridorEdges j₃ (L₃ + 1) with hGdef
  have hs1 : hrHD_corridorEdges j₁ (L₁ + 1) ⊆ G := by
    rw [hGdef]; exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hs2 : hrHD_corridorEdges j₂ (L₂ + 1) ⊆ G := by
    rw [hGdef]; exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hs3 : hrHD_corridorEdges j₃ (L₃ + 1) ⊆ G := by rw [hGdef]; exact Finset.subset_union_right
  have hne12 : (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₂ 1 :=
    bc2_rayCell_distinct_of_ne hj12 one_ne_zero
  have hne13 : (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₃ 1 :=
    bc2_rayCell_distinct_of_ne hj13 one_ne_zero
  have hne23 : (hrHD_rayPt j₂ 1 : Site d) ≠ hrHD_rayPt j₃ 1 :=
    bc2_rayCell_distinct_of_ne hj23 one_ne_zero
  refine ⟨hrHD_rayPt j₁ 1, hrHD_rayPt j₂ 1, hrHD_rayPt j₃ 1, G,
    hrHD_rayPt j₁ ((L₁ : ℤ) + 1), hrHD_rayPt j₂ ((L₂ : ℤ) + 1), hrHD_rayPt j₃ ((L₃ : ℤ) + 1),
    ⟨hne12, hne13, hne23⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    ⟨bc2_corridorChain_in_union j₁ L₁ G hs1, bc2_corridorChain_in_union j₂ L₂ G hs2,
      bc2_corridorChain_in_union j₃ L₃ G hs3⟩,
    ⟨?_, ?_, ?_⟩, hsep12, hsep13, hsep23⟩
  · exact bc2_clusterInfinite_force_mono_origin ω G hi1
  · exact bc2_clusterInfinite_force_mono_origin ω G hi2
  · exact bc2_clusterInfinite_force_mono_origin ω G hi3

/-- Every configuration of `threeMeetBox d n` has forced corridor routing. -/
def bc2_BoxForcedCorridorRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, bc2_ForcedCorridorRouting ω

lemma bc2_corridorCover_of_box {n : ℕ} (h : bc2_BoxForcedCorridorRouting d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G :=
  csc_corridorCover_of_distinctClusters
    (fun ω hω => bc2_csc_of_forcedCorridorRouting ω (h ω hω))

/-- Burton–Keane conclusion from forced corridor routing in every box and the counting hypotheses of
`burton_keane_uniqueness_full`. Those hypotheses are unsatisfiable for `d ≥ 1`
(`tfc_not_hbound_hdens`), so the statement has content only for `d = 0`. -/
lemma bc2_burtonKeane_uniqueness_of_box
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ n : ℕ, bc2_BoxForcedCorridorRouting d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_corridorCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc2_corridorCover_of_box (hroute n))

/-! ## C. Neighbour witnesses -/

lemma bc2_pairwiseSeparated_zero_of_cutDisconnected (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d)
    (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ 0 0 0 := by
  set G : Finset (Sym2 (Site d)) :=
    hrHD_corridorEdges j₁ (0 + 1) ∪ hrHD_corridorEdges j₂ (0 + 1) ∪
      hrHD_corridorEdges j₃ (0 + 1) with hGdef
  have hGmem : ∀ e ∈ G, (0 : Site d) ∈ e := by
    intro e he
    rw [hGdef, Finset.mem_union, Finset.mem_union] at he
    have hcorr : ∀ (j : Fin d), e ∈ hrHD_corridorEdges j (0 + 1) → (0 : Site d) ∈ e := by
      intro j hj
      rw [hrHD_corridorEdges, Finset.mem_image] at hj
      obtain ⟨t, ht, rfl⟩ := hj
      rw [Finset.mem_range] at ht
      have ht0 : t = 0 := by omega
      subst ht0
      rw [Sym2.mem_iff]; left
      simp
    rcases he with (h | h) | h
    · exact hcorr j₁ h
    · exact hcorr j₂ h
    · exact hcorr j₃ h
  have hrm : removeSite (0 : Site d) (forceOpenFinset G ω) = removeSite (0 : Site d) ω :=
    removeSite_forceOpen_eq 0 G hGmem ω
  refine ⟨?_, ?_, ?_⟩
  · change ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) _ _; rw [hrm]; exact hsep12
  · change ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) _ _; rw [hrm]; exact hsep13
  · change ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) _ _; rw [hrm]; exact hsep23

lemma bc2_forcedCorridorRouting_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite)
    (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    bc2_ForcedCorridorRouting ω := by
  have he : ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) := by norm_num
  refine ⟨j₁, j₂, j₃, 0, 0, 0, ⟨hj12, hj13, hj23⟩, ⟨?_, ?_, ?_⟩,
    bc2_pairwiseSeparated_zero_of_cutDisconnected ω j₁ j₂ j₃ hsep12 hsep13 hsep23⟩
  · rw [he]; exact hi1
  · rw [he]; exact hi2
  · rw [he]; exact hi3

lemma bc2_csc_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite)
    (hsep12 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
    (hsep13 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
    (hsep23 : ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
    csc_DistinctClusterCorridors ω :=
  bc2_csc_of_forcedCorridorRouting ω
    (bc2_forcedCorridorRouting_of_neighbour_witnesses ω hj12 hj13 hj23 hi1 hi2 hi3
      hsep12 hsep13 hsep23)

lemma bc2_core (n : ℕ) :
    (bc2_BoxForcedCorridorRouting d n →
        threeMeetBox d n ⊆
          ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
            CorridorWorks a₁ a₂ a₃ G) ∧
      (∀ {j₁ j₂ j₃ : Fin d} (ω : ConfigSpace (Sym2 (Site d))),
        j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite →
        ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) →
        ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) →
        ¬ Connected d (removeSite 0 ω) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) →
        csc_DistinctClusterCorridors ω) :=
  ⟨fun h => bc2_corridorCover_of_box h,
    fun ω hj12 hj13 hj23 hi1 hi2 hi3 hsep12 hsep13 hsep23 =>
      bc2_csc_neighbour_witnesses ω hj12 hj13 hj23 hi1 hi2 hi3 hsep12 hsep13 hsep23⟩

end Walls

end StatMech
