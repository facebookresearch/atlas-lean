/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Ising.GKS
import Code.Sharpness.CurrentRep
import Code.Ising.GHSThreePoint
import Code.Ising.GHSDistinctSite

open Finset SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



























theorem gc_ergrep (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
      = currentSum G β (fun _ => 1) A / currentSum G β (fun _ => 1) ∅ :=
  isingExpectation_eq_currentSum_ratio G β A










theorem gc_ergrep_currentSum_eq_betaWeight (β : ℝ) (A : Finset V) :
    currentSum G β (fun _ => 1) A
      = ∑' m : ↥G.edgeFinset → ℕ,
          if sources G (ofEdgeFun G m) = A then
            (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0 := by
  unfold currentSum
  refine tsum_congr (fun m => ?_)
  by_cases h : sources G (ofEdgeFun G m) = A
  · rw [if_pos h, if_pos h, weight_ofEdgeFun]
    exact Finset.prod_congr rfl (fun e _ => by rw [mul_one])
  · rw [if_neg h, if_neg h]





theorem gc_ergrep_betaWeight (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
      = (∑' m : ↥G.edgeFinset → ℕ,
            if sources G (ofEdgeFun G m) = A then
              (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0)
        / (∑' m : ↥G.edgeFinset → ℕ,
            if sources G (ofEdgeFun G m) = ∅ then
              (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0) := by
  rw [gc_ergrep, gc_ergrep_currentSum_eq_betaWeight, gc_ergrep_currentSum_eq_betaWeight]






theorem gc_ergrep_general (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G β J A = currentSum G β J A / currentSum G β J ∅ :=
  current_representation G β J A





theorem gc_ergrep_denom_pos (β : ℝ) : 0 < currentSum G β (fun _ => 1) ∅ := by
  have hP : partitionJ G β (fun _ => 1)
      = (2 : ℝ) ^ (Fintype.card V) * currentSum G β (fun _ => 1) ∅ :=
    partitionJ_eq_currentSum G β (fun _ => 1)
  have hPpos : 0 < partitionJ G β (fun _ => 1) := partitionJ_pos G β (fun _ => 1)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card V) := by positivity
  rw [hP] at hPpos
  exact (pos_iff_pos_of_mul_pos hPpos).mp h2

end StatMech.Walls
