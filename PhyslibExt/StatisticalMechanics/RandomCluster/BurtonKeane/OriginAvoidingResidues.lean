/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Finite.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors

/-!
# Avoiding residues from three clusters at the origin

When three distinct infinite clusters reach neighbours of the origin without using it, each gives an
avoiding routing residue and an avoiding attachment.

## i. Overview

In `removeSite 0 ω` the cluster of the origin is `{0}`, so a site with infinite cluster there is not
the origin. A neighbour `a` of the origin connected to `x` in `removeSite 0 ω`, with infinite
cluster, gives the residue `ava_AvoidingRoutingResidue ω x` and an avoiding attachment. Three
clusters reaching the origin (`mco_ThreeClustersReachOrigin`) give three residues, and the box
version follows.

## ii. Key results

- `arr_three_residues_of_reachOrigin` : three residues from three clusters reaching the origin.

## iii. Table of contents

- A. The cluster of the origin
- B. Residues from reach

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. The cluster of the origin -/

/-- Same statement as `bkm_cluster_removeSite_origin_eq_singleton`; kept because
`CorridorWitnessRemoveSite` is not imported by all its users. -/
lemma arr_cluster_removeSite_origin (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite 0 ω) (0 : Site d) = {(0 : Site d)} := by
  ext y
  simp only [mem_cluster, Set.mem_singleton_iff]
  constructor
  · intro h; exact (ava_connected_origin_eq ω h).symm ▸ rfl
  · intro h; subst h; exact connected_rfl

/-- Same statement as `bkm_cluster_removeSite_origin_finite`; kept because
`CorridorWitnessRemoveSite`
is not imported by all its users. -/
lemma arr_cluster_removeSite_origin_finite (ω : ConfigSpace (Sym2 (Site d))) :
    (cluster d (removeSite 0 ω) (0 : Site d)).Finite := by
  rw [arr_cluster_removeSite_origin]; exact Set.finite_singleton _

/-- Same statement as `bkm_witness_ne_zero`; kept because `CorridorWitnessRemoveSite` is not
imported by
all its users. -/
lemma arr_witness_ne_zero (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) : x ≠ 0 := by
  rintro rfl
  exact hinf (arr_cluster_removeSite_origin_finite ω)

/-! ## B. Residues from reach -/

lemma arr_routingResidue_of_reach (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hc : Connected d (removeSite 0 ω) a x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    ava_AvoidingRoutingResidue ω x :=
  ⟨arr_witness_ne_zero ω hinf, hinf, a, hadj, (mem_cluster.mpr hc.symm)⟩

lemma arr_avoidingAttachment_of_reach (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hc : Connected d (removeSite 0 ω) a x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x :=
  ava_avoidingAttachment ω x (arr_routingResidue_of_reach ω hadj hc hinf)

lemma arr_three_residues_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) :
    ∃ x₁ x₂ x₃ : Site d, ava_AvoidingRoutingResidue ω x₁ ∧
      ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, ⟨ha1, ha2, ha3⟩, ⟨hc1, hc2, hc3⟩,
    ⟨hi1, hi2, hi3⟩, _hdist⟩ := h
  exact ⟨x₁, x₂, x₃,
    arr_routingResidue_of_reach ω ha1 hc1 hi1,
    arr_routingResidue_of_reach ω ha2 hc2 hi2,
    arr_routingResidue_of_reach ω ha3 hc3 hi3⟩

lemma arr_three_avoidingAttachment_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) :
    ∃ x₁ x₂ x₃ : Site d, cla_AvoidingAttachment ω x₁ ∧
      cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃ := by
  obtain ⟨x₁, x₂, x₃, h1, h2, h3⟩ := arr_three_residues_of_reachOrigin ω h
  exact ⟨x₁, x₂, x₃, ava_avoidingAttachment ω x₁ h1, ava_avoidingAttachment ω x₂ h2,
    ava_avoidingAttachment ω x₃ h3⟩

lemma arr_boxAvoidingRoutingResidue_of_reach {n : ℕ}
    (hreach : ∀ ω ∈ threeMeetBox d n, mco_ThreeClustersReachOrigin ω) :
    ∀ ω ∈ threeMeetBox d n, ∃ x₁ x₂ x₃ : Site d,
      ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
        ava_AvoidingRoutingResidue ω x₃ :=
  fun ω hω => arr_three_residues_of_reachOrigin ω (hreach ω hω)

lemma arr_three_residues_satisfiable (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (h1 : (hypercubicLattice d).Adj 0 x₁) (h2 : (hypercubicLattice d).Adj 0 x₂)
    (h3 : (hypercubicLattice d).Adj 0 x₃)
    (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
    ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
      ava_AvoidingRoutingResidue ω x₃ :=
  ⟨StatMech.Percolation.ava_avoidingRoutingResidue_of_neighbour ω x₁ h1 hi1,
      StatMech.Percolation.ava_avoidingRoutingResidue_of_neighbour ω x₂ h2 hi2,
    StatMech.Percolation.ava_avoidingRoutingResidue_of_neighbour ω x₃ h3 hi3⟩

end Percolation

end StatMech
