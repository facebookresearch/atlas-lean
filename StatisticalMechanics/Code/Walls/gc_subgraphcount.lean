/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.SwitchingCovariance

open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


















theorem gc_binom_eq_subgraph_count (m n : ↥G.edgeFinset → ℕ) :
    #((univ : Finset (Finset (Copy G m))).filter (fun N => profileFlux G m N = n))
      = ∏ e : ↥G.edgeFinset, (m e).choose (n e) := by
  rw [Finset.card_filter]
  have h := preimage_count G m n
  rw [Finset.card_filter] at h
  exact h












theorem gc_boundary_iff_profile (m : ↥G.edgeFinset → ℕ) (B : Finset V) (N : Finset (Copy G m)) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B
      ↔ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N)) = B := by
  rw [sources_eq]

























theorem gc_subgraph_count (m : ↥G.edgeFinset → ℕ) (B : Finset V) :
    (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B
          then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0))
      = #((univ : Finset (Finset (Copy G m))).filter
          (fun N => StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B)) := by
  
  have hbridge := flux_edgecopy_bridge G m (M := ℕ)
    (fun n => if StatMech.Sharpness.sources G (ofEdgeFun G n) = B then (1 : ℕ) else 0)
  simp only [smul_eq_mul] at hbridge
  
  have hLHS : (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e))
          * (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B then (1 : ℕ) else 0))
      = (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B
          then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B <;> simp [h]
  rw [← hLHS, hbridge]
  
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [sources_eq]
















theorem gc_subgraph_count_eq_sum_over_profiles (m : ↥G.edgeFinset → ℕ) (B : Finset V) :
    #((univ : Finset (Finset (Copy G m))).filter
          (fun N => StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B))
      = ∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m},
          (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B
            then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0) :=
  (gc_subgraph_count G m B).symm

end StatMech.Walls
