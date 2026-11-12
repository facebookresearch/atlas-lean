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

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]























theorem hdc_signSwap (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
    (A : Finset V) (hm : Sharpness.sources G m = A) {u v : V} (huv : u ≠ v)
    (hconn : connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
    hnw_mass G β J m (A ∆ {u, v}) ≤ hnw_mass G β J m A :=
  asd_signDominance_native G β J hβ hJ m hnd 1 (by norm_num) A hm huv hconn

















theorem hdc_reroute_eq_base_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hall : hnw_allConn G m o x y) :
    hnw_mass G β J m (A ∆ {x, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, x}) = hnw_mass G β J m A :=
  hnw_allMass_eq_paired G β J m A hox hoy hxy hall
















theorem hdc_allConn_self_domination (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y),
          (hnw_mass G β J m (A ∆ {x, y}) + hnw_mass G β J m (A ∆ {o, y})
            + hnw_mass G β J m (A ∆ {o, x})) := by
  have hkey : ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y),
        (hnw_mass G β J m (A ∆ {x, y}) + hnw_mass G β J m (A ∆ {o, y})
          + hnw_mass G β J m (A ∆ {o, x}))
      = 3 * ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hmem => ?_)
    rw [Finset.mem_filter] at hmem
    obtain ⟨e1, e2, e3⟩ := hdc_reroute_eq_base_allConn G β J m A hox hoy hxy hmem.2
    rw [e1, e2, e3]; ring
  rw [hkey]
  have hnn : 0 ≤ ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A :=
    Finset.sum_nonneg (fun m _ => hnw_mass_nonneg G β J hβ hJ m A)
  linarith







theorem hdc_allConn_gap_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (A : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m A o x y ≤ 0 := by
  rw [hnw_gap_allConn G β J m A hox hoy hxy hall]
  have := hnw_mass_nonneg G β J hβ hJ m A
  linarith





theorem hdc_allConn_summed_gap_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m A o x y ≤ 0 := by
  apply Finset.sum_nonpos
  intro m hmem
  rw [Finset.mem_filter] at hmem
  exact hdc_allConn_gap_nonpos G β J hβ hJ m A hox hoy hxy hmem.2














theorem hdc_allConn_mass_le_full (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) {o x y : V} :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A
      ≤ ∑ m ∈ M, hnw_mass G β J m A :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun m _ _ => hnw_mass_nonneg G β J hβ hJ m A)













theorem hdc_pairwise_full_dom (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A) {u v : V} (huv : u ≠ v)
    (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v
        ↔ connP (posEdges G.edgeFinset m) u v) :
    ∑ m ∈ M, hnw_mass G β J m (A ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
  refine Finset.sum_le_sum (fun m hmem => ?_)
  by_cases hc : connP (oddEdges G.edgeFinset m) u v
  · exact hdc_signSwap G β J hβ hJ m (hnd m hmem) A (hm m hmem) huv (Or.inl hc)
  · exact hdc_signSwap G β J hβ hJ m (hnd m hmem) A (hm m hmem) huv
      (Or.inr (fun h => hc ((hcoh m hmem).mpr h)))





theorem hdc_ghs_singlePair (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A)
      ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A)
      ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}) ≤ ∑ m ∈ M, hnw_mass G β J m A) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hdc_pairwise_full_dom G β J hβ hJ M hnd A hm hxy (fun m hmem => (hcoh m hmem).1)
  · exact hdc_pairwise_full_dom G β J hβ hJ M hnd A hm hoy (fun m hmem => (hcoh m hmem).2.1)
  · exact hdc_pairwise_full_dom G β J hβ hJ M hnd A hm hox (fun m hmem => (hcoh m hmem).2.2)

















theorem hdc_hdom_cross_class_refutable :
    ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter
            (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
        ≤ ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter
            (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) :=
  hmu_hdom_refutable



















theorem hdc_ghs_distinct_site_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}))
      ≤ ∑ m ∈ M, hnw_mass G β J m A :=
  hnw_ghs_distinct_site_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom

end Ising

end StatMech
