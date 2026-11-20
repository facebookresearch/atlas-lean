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

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














noncomputable def tcp_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) : ℝ :=
  ∑ m ∈ M, hnw_mass G β J m B




noncomputable def tcp_allConnMass (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B




noncomputable def tcp_allConnProb (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  tcp_allConnMass G β J M B o x y / tcp_partitionFunction G β J M B



theorem tcp_partitionFunction_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) :
    0 ≤ tcp_partitionFunction G β J M B :=
  Finset.sum_nonneg (fun m _ => hnw_mass_nonneg G β J hβ hJ m B)




theorem tcp_allConnMass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnMass G β J M B o x y :=
  Finset.sum_nonneg (fun m _ => hnw_mass_nonneg G β J hβ hJ m B)














theorem tcp_allConnMass_le_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnMass G β J M B o x y ≤ tcp_partitionFunction G β J M B :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun m _ _ => hnw_mass_nonneg G β J hβ hJ m B)







theorem tcp_allConn_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 := by
  unfold tcp_allConnProb
  rcases eq_or_lt_of_le (tcp_partitionFunction_nonneg G β J hβ hJ M B) with hZ | hZ
  · 
    rw [← hZ, div_zero]; norm_num
  · 
    rw [div_le_one hZ]
    exact tcp_allConnMass_le_partitionFunction G β J hβ hJ M B o x y





theorem tcp_allConn_prob_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    0 ≤ tcp_allConnProb G β J M B o x y :=
  div_nonneg (tcp_allConnMass_nonneg G β J hβ hJ M B o x y)
    (tcp_partitionFunction_nonneg G β J hβ hJ M B)
















theorem tcp_lebowitz_summed_gap (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y
      = -2 * tcp_allConnMass G β J M B o x y := by
  unfold tcp_allConnMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hmem => ?_)
  rw [Finset.mem_filter] at hmem
  exact hnw_gap_allConn G β J m B hox hoy hxy hmem.2






theorem tcp_lebowitz_sign (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y ≤ 0 := by
  rw [tcp_lebowitz_summed_gap G β J M B hox hoy hxy]
  have := tcp_allConnMass_nonneg G β J hβ hJ M B o x y
  linarith













theorem tcp_reroute_sum_eq_three_allConnMass (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {x, y}))
      + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, y}))
      + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, x}))
      = 3 * tcp_allConnMass G β J M B o x y := by
  unfold tcp_allConnMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hmem => ?_)
  rw [Finset.mem_filter] at hmem
  obtain ⟨e1, e2, e3⟩ := hnw_allMass_eq_paired G β J m B hox hoy hxy hmem.2
  rw [e1, e2, e3]; ring
















theorem tcp_ghs_distinct_site (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B
      ≤ (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {x, y}))
        + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, y}))
        + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, x})) := by
  rw [tcp_reroute_sum_eq_three_allConnMass G β J M B hox hoy hxy]
  have hN : 0 ≤ tcp_allConnMass G β J M B o x y :=
    tcp_allConnMass_nonneg G β J hβ hJ M B o x y
  have : tcp_allConnMass G β J M B o x y ≤ 3 * tcp_allConnMass G β J M B o x y := by linarith
  
  simpa only [tcp_allConnMass] using this
























theorem tcp_per_current_dom (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : Sharpness.sources G m = B) {u v : V} (huv : u ≠ v)
    (hconn : connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
    hnw_mass G β J m (B ∆ {u, v}) ≤ hnw_mass G β J m B :=
  asd_signDominance_native G β J hβ hJ m hnd 1 (by norm_num) B hm huv hconn













theorem tcp_family_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {u v : V} (huv : u ≠ v)
    (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v
        ↔ connP (posEdges G.edgeFinset m) u v) :
    ∑ m ∈ M, hnw_mass G β J m (B ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m B := by
  refine Finset.sum_le_sum (fun m hmem => ?_)
  by_cases hc : connP (oddEdges G.edgeFinset m) u v
  · exact tcp_per_current_dom G β J hβ hJ m (hnd m hmem) B (hm m hmem) huv (Or.inl hc)
  · exact tcp_per_current_dom G β J hβ hJ m (hnd m hmem) B (hm m hmem) huv
      (Or.inr (fun h => hc ((hcoh m hmem).mpr h)))























theorem tcp_prob_bound_closes_lebowitz (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y
      ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
  have hP0 : 0 ≤ tcp_allConnProb G β J M B o x y :=
    tcp_allConn_prob_nonneg G β J hβ hJ M B o x y
  have hP1 : tcp_allConnProb G β J M B o x y ≤ 1 :=
    tcp_allConn_prob_le_one G β J hβ hJ M B o x y
  constructor
  · 
    nlinarith [mul_nonneg hμ (sub_nonneg.mpr hP1)]
  · 
    nlinarith [mul_nonneg hμ hP0]

end Ising

end StatMech
