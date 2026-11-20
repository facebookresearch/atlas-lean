/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Percolation.AvoidingAttachment
import Code.Percolation.MengerCorridors

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}









theorem arr_cluster_removeSite_origin (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite 0 ω) (0 : Site d) = {(0 : Site d)} := by
  ext y
  simp only [mem_cluster, Set.mem_singleton_iff]
  constructor
  · intro h; exact (ava_connected_origin_eq ω h).symm ▸ rfl
  · intro h; subst h; exact connected_rfl



theorem arr_cluster_removeSite_origin_finite (ω : ConfigSpace (Sym2 (Site d))) :
    (cluster d (removeSite 0 ω) (0 : Site d)).Finite := by
  rw [arr_cluster_removeSite_origin]; exact Set.finite_singleton _




theorem arr_witness_ne_zero (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) : x ≠ 0 := by
  rintro rfl
  exact hinf (arr_cluster_removeSite_origin_finite ω)














theorem arr_routingResidue_of_reach (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hc : Connected d (removeSite 0 ω) a x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    ava_AvoidingRoutingResidue ω x :=
  ⟨arr_witness_ne_zero ω hinf, hinf, a, hadj, (mem_cluster.mpr hc.symm)⟩



theorem arr_avoidingAttachment_of_reach (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hc : Connected d (removeSite 0 ω) a x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x :=
  ava_avoidingAttachment ω x (arr_routingResidue_of_reach ω hadj hc hinf)













theorem arr_three_residues_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) :
    ∃ x₁ x₂ x₃ : Site d, ava_AvoidingRoutingResidue ω x₁ ∧
      ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, ⟨ha1, ha2, ha3⟩, ⟨hc1, hc2, hc3⟩,
    ⟨hi1, hi2, hi3⟩, _hdist⟩ := h
  exact ⟨x₁, x₂, x₃,
    arr_routingResidue_of_reach ω ha1 hc1 hi1,
    arr_routingResidue_of_reach ω ha2 hc2 hi2,
    arr_routingResidue_of_reach ω ha3 hc3 hi3⟩




theorem arr_three_avoidingAttachment_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) :
    ∃ x₁ x₂ x₃ : Site d, cla_AvoidingAttachment ω x₁ ∧
      cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃ := by
  obtain ⟨x₁, x₂, x₃, h1, h2, h3⟩ := arr_three_residues_of_reachOrigin ω h
  exact ⟨x₁, x₂, x₃, ava_avoidingAttachment ω x₁ h1, ava_avoidingAttachment ω x₂ h2,
    ava_avoidingAttachment ω x₃ h3⟩














theorem arr_boxAvoidingRoutingResidue_of_reach {n : ℕ}
    (hreach : ∀ ω ∈ threeMeetBox d n, mco_ThreeClustersReachOrigin ω) :
    ∀ ω ∈ threeMeetBox d n, ∃ x₁ x₂ x₃ : Site d,
      ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
        ava_AvoidingRoutingResidue ω x₃ :=
  fun ω hω => arr_three_residues_of_reachOrigin ω (hreach ω hω)













theorem arr_routingResidue_satisfiable (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    ava_AvoidingRoutingResidue ω x :=
  arr_routingResidue_of_reach ω hadj connected_rfl hinf





theorem arr_three_residues_satisfiable (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (h1 : (hypercubicLattice d).Adj 0 x₁) (h2 : (hypercubicLattice d).Adj 0 x₂)
    (h3 : (hypercubicLattice d).Adj 0 x₃)
    (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
    ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
      ava_AvoidingRoutingResidue ω x₃ :=
  ⟨arr_routingResidue_satisfiable ω x₁ h1 hi1, arr_routingResidue_satisfiable ω x₂ h2 hi2,
    arr_routingResidue_satisfiable ω x₃ h3 hi3⟩

end Percolation

end StatMech
