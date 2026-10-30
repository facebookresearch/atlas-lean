/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationFiniteEnergy

/-!
# Axis assignments for three infinite clusters

An assignment of three distinct axes to three infinite clusters that run along them gives the box
attachment data and disjoint routing.

## i. Overview

`lmg_BoxAxisAssignment d n` asks that in every configuration with three distinct infinite clusters
meeting `B_n`, the clusters run along three distinct axes. Corridors along distinct axes are
disjoint, so this gives attachment data at the origin and `hrHD_DisjointRouting`. A Hall-type
candidate condition on the axes suffices for the assignment.

## ii. Key results

- `lmg_corridors_disjoint` : corridors along distinct axes are disjoint
- `lmg_disjointRouting_of_assignment` : an axis assignment gives disjoint routing
- `lmg_axisAssignment_of_candidates` : candidate axes give an axis assignment

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma lmg_corridors_disjoint {j₁ j₂ j₃ : Fin d}
    (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃) (L : ℕ) :
    (Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) ∧
      Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₃ L) ∧
      Disjoint (lma_corridorVerts j₂ L) (lma_corridorVerts j₃ L)) ∧
    ((0 : Site d) ∉ lma_corridorVerts j₁ L ∧ (0 : Site d) ∉ lma_corridorVerts j₂ L ∧
      (0 : Site d) ∉ lma_corridorVerts j₃ L) :=
  ⟨⟨lma_corridorVerts_disjoint hjd12 L, lma_corridorVerts_disjoint hjd13 L,
      lma_corridorVerts_disjoint hjd23 L⟩,
    lma_origin_notMem_corridorVerts j₁ L, lma_origin_notMem_corridorVerts j₂ L,
    lma_origin_notMem_corridorVerts j₃ L⟩

lemma lmg_attachData (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : crr_AxisAssignment ω x₁ j₁) (h2 : crr_AxisAssignment ω x₂ j₂)
    (h3 : crr_AxisAssignment ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ :=
  lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23
    (crr_clusterReachesRay_of_assignment ω x₁ j₁ h1)
    (crr_clusterReachesRay_of_assignment ω x₂ j₂ h2)
    (crr_clusterReachesRay_of_assignment ω x₃ j₃ h3)

lemma lmg_attachData_of_candidates (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (S : Fin 3 → Finset (Fin d))
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    tex_AttachData ω x₁ x₂ x₃ :=
  caa_attachData ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 h

lemma lmg_attachData_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : crr_AxisAssignment ω x₁ j₁) (h2 : crr_AxisAssignment ω x₂ j₂)
    (h3 : crr_AxisAssignment ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ ∧
      ∀ L : ℕ,
        (Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) ∧
          Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₃ L) ∧
          Disjoint (lma_corridorVerts j₂ L) (lma_corridorVerts j₃ L)) ∧
        ((0 : Site d) ∉ lma_corridorVerts j₁ L ∧ (0 : Site d) ∉ lma_corridorVerts j₂ L ∧
          (0 : Site d) ∉ lma_corridorVerts j₃ L) :=
  ⟨lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3,
    fun L => lmg_corridors_disjoint hjd12 hjd13 hjd23 L⟩

lemma lmg_threeClustersReachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : crr_AxisAssignment ω x₁ j₁) (h2 : crr_AxisAssignment ω x₂ j₂)
    (h3 : crr_AxisAssignment ω x₃ j₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ ⟨hcd12, hcd13, hcd23⟩
    (lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3)

/-- In every configuration with three distinct infinite clusters meeting `B_n`, the clusters run
along three distinct coordinate axes. -/
def lmg_BoxAxisAssignment (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ∃ j₁ j₂ j₃ : Fin d, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
        crr_AxisAssignment ω x₁ j₁ ∧ crr_AxisAssignment ω x₂ j₂ ∧ crr_AxisAssignment ω x₃ j₃

lemma lmg_boxAttachData_of_assignment {n : ℕ}
    (h : lmg_BoxAxisAssignment d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, _, ha1, ha2, ha3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 ha1 ha2 ha3

lemma lmg_disjointRouting_of_assignment {n : ℕ}
    (h : lmg_BoxAxisAssignment d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box (lmg_boxAttachData_of_assignment h)

lemma lmg_boxAttachData_of_candidates {n : ℕ}
    (h : caa_BoxRunsAlongCandidates d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨S, hcand⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lmg_attachData_of_candidates ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 hcand

lemma lmg_disjointRouting_of_candidates {n : ℕ}
    (h : caa_BoxRunsAlongCandidates d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box (lmg_boxAttachData_of_candidates h)

lemma lmg_axisAssignment_of_candidates (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (S : Fin 3 → Finset (Fin d))
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    ∃ j₁ j₂ j₃ : Fin d, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      crr_AxisAssignment ω x₁ j₁ ∧ crr_AxisAssignment ω x₂ j₂ ∧ crr_AxisAssignment ω x₃ j₃ := by
  obtain ⟨f, hinj, hf⟩ := caa_axisAssignment ω ![x₁, x₂, x₃] S h
  refine ⟨f 0, f 1, f 2, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro he; exact absurd (hinj he) (by decide)
  · intro he; exact absurd (hinj he) (by decide)
  · intro he; exact absurd (hinj he) (by decide)
  · exact hf 0
  · exact hf 1
  · exact hf 2

lemma lmg_boxAxisAssignment_of_candidates {n : ℕ}
    (h : caa_BoxRunsAlongCandidates d n) : lmg_BoxAxisAssignment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨S, hcand⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lmg_axisAssignment_of_candidates ω x₁ x₂ x₃ S hcand

lemma lmg_axisAssignment_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      crr_AxisAssignment ω (hrHD_rayPt j₁ 1) j₁ ∧
      crr_AxisAssignment ω (hrHD_rayPt j₂ 1) j₂ ∧
      crr_AxisAssignment ω (hrHD_rayPt j₃ 1) j₃ :=
  ⟨⟨hjd12, hjd13, hjd23⟩, crr_runsAlongAxis_of_neighbour ω j₁ hi1,
    crr_runsAlongAxis_of_neighbour ω j₂ hi2, crr_runsAlongAxis_of_neighbour ω j₃ hi3⟩

lemma lmg_neighbour_witnesses_distinct {j₁ j₂ j₃ : Fin d}
    (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃) :
    (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₂ 1 ∧
      (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₃ 1 ∧
      (hrHD_rayPt j₂ 1 : Site d) ≠ hrHD_rayPt j₃ 1 :=
  ⟨hrHD_rayPt_one_ne_of_ne hjd12, hrHD_rayPt_one_ne_of_ne hjd13, hrHD_rayPt_one_ne_of_ne hjd23⟩

end Percolation

end StatMech
