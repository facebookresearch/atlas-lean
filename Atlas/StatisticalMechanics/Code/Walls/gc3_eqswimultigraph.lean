/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Walls.gc2_core
import Code.Walls.gc2_shiftbij
import Code.Walls.gc_subgraphcount
import Code.Sharpness.MultiReplica

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]
















theorem gc3_count_collapse_of_FB (ends : ι → Sym2 V) (M : Finset ι) {B : Finset V}
    (hFB : gc2_FB ends M B) :
    #(M.powerset.filter (fun N => sources ends N = B))
      = #(M.powerset.filter (fun N => sources ends N = ∅)) := by
  
  obtain ⟨K, hKM, hKsrc⟩ := gc2_minlenDisjoint_K_exists ends M B hFB
  
  exact gc2_count_B_eq_count_empty_of_K ends M K hKM hKsrc







theorem gc3_count_zero_of_not_FB (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {B : Finset V} (hFB : ¬ gc2_FB ends M B) :
    #(M.powerset.filter (fun N => sources ends N = B)) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro N hNpow hNsrc
  rw [Finset.mem_powerset] at hNpow
  
  exact hFB (gc2_K_exists_imp_FB ends M N hNpow hnd hNsrc)


















theorem gc3_eqSwi_multigraph (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) (B : Finset V) :
    #(M.powerset.filter (fun N => sources ends N = B))
      = (if gc2_FB ends M B then 1 else 0)
          * #(M.powerset.filter (fun N => sources ends N = ∅)) := by
  by_cases hFB : gc2_FB ends M B
  · rw [if_pos hFB, one_mul]
    exact gc3_count_collapse_of_FB ends M hFB
  · rw [if_neg hFB, zero_mul]
    exact gc3_count_zero_of_not_FB ends M hnd hFB















theorem gc3_eqSwi_multigraph_current {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (M : Finset (Copy G m)) (B : Finset W) :
    #(M.powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = B))
      = (if gc2_FB (endsM G m) M B then 1 else 0)
          * #(M.powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = ∅)) :=
  gc3_eqSwi_multigraph (endsM G m) M (fun i _ => endsM_not_isDiag G m i) B










theorem gc3_eqSwi_multigraph_univ {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (B : Finset W) :
    #((Finset.univ : Finset (Copy G m)).powerset.filter
        (fun N => RandomCurrent.sources (endsM G m) N = B))
      = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) B then 1 else 0)
          * #((Finset.univ : Finset (Copy G m)).powerset.filter
              (fun N => RandomCurrent.sources (endsM G m) N = ∅)) :=
  gc3_eqSwi_multigraph_current G m (Finset.univ : Finset (Copy G m)) B


















theorem gc3_eqSwi_split {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (B : Finset W) :
    (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B
          then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0))
      = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) B then 1 else 0)
        * (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
          (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = ∅
            then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0)) := by
  rw [StatMech.Walls.gc_subgraph_count G m B, StatMech.Walls.gc_subgraph_count G m ∅]
  have huniv : (Finset.univ : Finset (Copy G m)).powerset = Finset.univ := by
    ext N; simp
  have h := gc3_eqSwi_multigraph_univ G m B
  rw [huniv] at h
  exact_mod_cast h






















theorem gc3_threeReplica_binomFactor {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m n₁ : ↥G.edgeFinset → ℕ) :
    (∏ e : ↥G.edgeFinset, ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁) e.1))
      = ∏ e : ↥G.edgeFinset, (m e).choose (n₁ e) := by
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold ofEdgeFun; rw [dif_pos e.2, dif_pos e.2]















theorem gc3_eqSwi_split_threeReplica {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (A : Finset W) :
    (∑ n₁ : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if StatMech.Sharpness.sources G (ofEdgeFun G n₁.1) = A
          then (∏ e : ↥G.edgeFinset,
                  ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁.1) e.1)) else 0))
      = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) A then 1 else 0)
        * (∑ n₁ : {p : ↥G.edgeFinset → ℕ // p ≤ m},
          (if StatMech.Sharpness.sources G (ofEdgeFun G n₁.1) = ∅
            then (∏ e : ↥G.edgeFinset,
                    ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁.1) e.1)) else 0)) := by
  
  have hread : ∀ n₁ : {p : ↥G.edgeFinset → ℕ // p ≤ m},
      (∏ e : ↥G.edgeFinset, ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁.1) e.1))
        = ∏ e : ↥G.edgeFinset, (m e).choose (n₁.1 e) :=
    fun n₁ => gc3_threeReplica_binomFactor G m n₁.1
  simp only [hread]
  
  exact gc3_eqSwi_split G m A

end StatMech.Walls
