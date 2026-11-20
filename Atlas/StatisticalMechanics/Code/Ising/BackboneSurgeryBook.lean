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
import Code.Ising.BackboneResummation
import Code.Ising.HdomMultiplicity

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
























theorem bsb_BackboneSurgery_refutable :
    ¬ bbr_BackboneSurgery hmu_TriG 1 (fun _ => 1)
        ({hmu_triM} : Finset (Current (Fin 3))) ∅ 0 1 2 := by
  intro hsurg
  
  have hdom := bbr_hdom_of_surgery hmu_TriG 1 (fun _ => 1) (by norm_num)
    (by intro e; norm_num) ({hmu_triM} : Finset (Current (Fin 3))) ∅ 0 1 2 hsurg
  
  exact hmu_hdom_refutable hdom

















theorem bsb_gap_allConn_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (A : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m A o x y ≤ 0 := by
  rw [hnw_gap_allConn G β J m A hox hoy hxy hall]
  have := hnw_mass_nonneg G β J hβ hJ m A
  linarith





















theorem bsb_pairwise_switching_dom (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A) {u v : V} (huv : u ≠ v)
    (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v
        ↔ connP (posEdges G.edgeFinset m) u v) :
    ∑ m ∈ M, hnw_mass G β J m (A ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
  refine Finset.sum_le_sum (fun m hmem => ?_)
  by_cases hc : connP (oddEdges G.edgeFinset m) u v
  · 
    rw [hnw_switching G β J m huv hc A]
  · 
    rw [hnw_mass_vanish G β J m (hnd m hmem) A (hm m hmem) huv
      (fun h => hc ((hcoh m hmem).mpr h))]
    exact hnw_mass_nonneg G β J hβ hJ m A








theorem bsb_ghs_singlePair_le (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A)
      ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A)
      ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}) ≤ ∑ m ∈ M, hnw_mass G β J m A) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bsb_pairwise_switching_dom G β J hβ hJ M hnd A hm hxy
      (fun m hmem => (hcoh m hmem).1)
  · exact bsb_pairwise_switching_dom G β J hβ hJ M hnd A hm hoy
      (fun m hmem => (hcoh m hmem).2.1)
  · exact bsb_pairwise_switching_dom G β J hβ hJ M hnd A hm hox
      (fun m hmem => (hcoh m hmem).2.2)





























theorem bsb_ghs_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
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
