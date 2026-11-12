/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Ising.TwoReplica
import Code.Ising.TwoReplicaWeighted
import Code.Ising.AizenmanSignDominance
import Code.Ising.HdomNativeWeight
import Code.Ising.HdomMultiplicity
import Code.Ising.TwoCurrentProbBound

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




















theorem cch_allConn_reroute_eq_base (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hall : hnw_allConn G m o x y) :
    hnw_mass G β J m (B ∆ {x, y}) = hnw_mass G β J m B
      ∧ hnw_mass G β J m (B ∆ {o, y}) = hnw_mass G β J m B
      ∧ hnw_mass G β J m (B ∆ {o, x}) = hnw_mass G β J m B :=
  hnw_allMass_eq_paired G β J m B hox hoy hxy hall



















theorem cch_crossClass_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
      ≤ (∑ m ∈ M, hnw_mass G β J m (B ∆ {x, y}))
        + (∑ m ∈ M, hnw_mass G β J m (B ∆ {o, y}))
        + (∑ m ∈ M, hnw_mass G β J m (B ∆ {o, x})) := by
  
  have hsub : ∀ S : Finset V,
      (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m S)
        ≤ ∑ m ∈ M, hnw_mass G β J m S :=
    fun S => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun m _ _ => hnw_mass_nonneg G β J hβ hJ m S)
  
  have hxy_re : (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {x, y}))
      = ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    exact (cch_allConn_reroute_eq_base G β J m B hox hoy hxy hm.2).1
  have hoy_re : (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, y}))
      = ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    exact (cch_allConn_reroute_eq_base G β J m B hox hoy hxy hm.2).2.1
  have hox_re : (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, x}))
      = ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    exact (cch_allConn_reroute_eq_base G β J m B hox hoy hxy hm.2).2.2
  have h1 := hsub (B ∆ {x, y}); rw [hxy_re] at h1
  have h2 := hsub (B ∆ {o, y}); rw [hoy_re] at h2
  have h3 := hsub (B ∆ {o, x}); rw [hox_re] at h3
  have hN : 0 ≤ ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B :=
    Finset.sum_nonneg (fun m _ => hnw_mass_nonneg G β J hβ hJ m B)
  linarith












theorem cch_allConnMass_le_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B :=
  tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y







theorem cch_crossClass_full_dom (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    2 * tcp_allConnMass G β J M B o x y
      ≤ tcp_partitionFunction G β J M B + tcp_allConnMass G β J M B o x y := by
  have hNZ := cch_allConnMass_le_partitionFunction G β J hβ hJ M B o x y
  have hN := tcp_allConnMass_nonneg G β J hβ hJ M B o x y
  linarith





theorem cch_allConn_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  tcp_allConn_prob_le_one G β J hβ hJ M B o x y








theorem cch_lebowitz_summed_gap (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y
      = -2 * tcp_allConnMass G β J M B o x y :=
  tcp_lebowitz_summed_gap G β J M B hox hoy hxy





theorem cch_lebowitz_sign (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y ≤ 0 :=
  tcp_lebowitz_sign G β J hβ hJ M B hox hoy hxy













theorem cch_per_current_dom (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : Sharpness.sources G m = B) {u v : V} (huv : u ≠ v)
    (hconn : connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
    hnw_mass G β J m (B ∆ {u, v}) ≤ hnw_mass G β J m B :=
  asd_signDominance_native G β J hβ hJ m hnd 1 (by norm_num) B hm huv hconn











theorem cch_eq_gri2_family (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {u v : V} (huv : u ≠ v)
    (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v
        ↔ connP (posEdges G.edgeFinset m) u v) :
    ∑ m ∈ M, hnw_mass G β J m (B ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m B := by
  refine Finset.sum_le_sum (fun m hmem => ?_)
  by_cases hc : connP (oddEdges G.edgeFinset m) u v
  · exact cch_per_current_dom G β J hβ hJ m (hnd m hmem) B (hm m hmem) huv (Or.inl hc)
  · exact cch_per_current_dom G β J hβ hJ m (hnd m hmem) B (hm m hmem) huv
      (Or.inr (fun h => hc ((hcoh m hmem).mpr h)))



















theorem cch_lebowitz_closes_U4 (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y
      ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  tcp_prob_bound_closes_lebowitz G β J hβ hJ M B o x y μ hμ













theorem cch_crossClass_dom_iff_le (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    (2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
        ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B)
      ↔ 0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y := by
  rw [hnw_inclusion_exclusion_decomp G β J M hnd B hm hox hoy hxy hcoh]
  constructor
  · intro h; linarith
  · intro h; linarith












theorem cch_full_gap_can_be_negative :
    ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))),
        hnw_gap hmu_TriG 1 (fun _ => 1) m ∅ 0 1 2 < 0 := by
  rw [Finset.sum_singleton]
  rw [hnw_gap_allConn hmu_TriG 1 (fun _ => 1) hmu_triM ∅ (by decide) (by decide) (by decide)
    hmu_tri_allConn]
  have hmass_pos : 0 < hnw_mass hmu_TriG 1 (fun _ => 1) hmu_triM ∅ := by
    have := hmu_mass_pos hmu_TriG 1 (fun _ => 1) (by norm_num) (by intro e; norm_num) hmu_triM
    rwa [hmu_tri_src] at this
  linarith









theorem cch_hdom_cross_class_refutable :
    ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter
            (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
        ≤ ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter
            (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) :=
  hmu_hdom_refutable

end Ising

end StatMech
