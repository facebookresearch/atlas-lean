/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Sharpness.CurrentRep
import Code.Walls.gc6_ghostgraph

open Finset BigOperators SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]













theorem gc9_sourceless_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) :
    0 < Sharpness.currentSum G β J ∅ := by
  have h := Sharpness.partitionJ_eq_currentSum G β J
  have hpos := Sharpness.partitionJ_pos G β J
  rw [h] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card V) := by positivity
  nlinarith [hpos, h2]
























theorem gc9_eq15_insertion_of_ne (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
    Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
  rw [Sharpness.current_representation, div_mul_cancel₀ _ h0]
















theorem gc9_eq15_insertion (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ :=
  gc9_eq15_insertion_of_ne G β J A (ne_of_gt (gc9_sourceless_pos G β J))













theorem gc9_currentSum_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    0 ≤ Sharpness.currentSum G β J A := by
  unfold Sharpness.currentSum
  refine tsum_nonneg (fun m => ?_)
  by_cases h : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A
  · rw [if_pos h]
    exact Finset.prod_nonneg (fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (by positivity))
  · rw [if_neg h]






theorem gc9_expectationJ_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    0 ≤ Sharpness.expectationJ G β J A := by
  rw [Sharpness.current_representation]
  exact div_nonneg (gc9_currentSum_nonneg G β J hβ hJ A)
    (gc9_currentSum_nonneg G β J hβ hJ ∅)






















theorem gc9_eq15_insertion_ghost (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (y : V) :
    Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb))
      = isingExpectation G β h (fun s => spin s y)
        * Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  rw [gc9_eq15_insertion (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc6_ghostGraph_dictionary G β h y]










theorem gc9_eq15_insertion_nonvacuous (β : ℝ) (J : Sym2 (Fin 4) → ℝ) :
    Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4))
      = Sharpness.expectationJ (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4))
        * Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ∅ :=
  gc9_eq15_insertion (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4))

end StatMech.Walls
