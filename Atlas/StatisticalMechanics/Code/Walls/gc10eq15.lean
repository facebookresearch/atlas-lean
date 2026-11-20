/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Mathlib
import Code.Sharpness.CurrentRep
import Code.Sharpness.TwoReplica
import Code.Walls.gc9eq15insertion
import Code.Walls.gc6_ghostgraph

open Finset BigOperators SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]



















theorem gc10_eq15_sourceRemoval (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.currentSum G β J A
      = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ :=
  gc9_eq15_insertion G β J A


















theorem gc10_eq15_ghost (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) (A : Finset (Option V)) :
    Sharpness.currentSum (withGhost G) β J A
      = Sharpness.expectationJ (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J ∅ :=
  gc9_eq15_insertion (withGhost G) β J A


















theorem gc10_currentMass_product_eq_sourcePairSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) (A B : Finset (Option V)) :
    Sharpness.currentSum (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J B
      = Sharpness.sourcePairSum (withGhost G) β J A B :=
  (Sharpness.sourcePairSum_eq_mul (withGhost G) β J A B).symm










theorem gc10_eq15_product_two_currentMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) (A B : Finset (Option V)) :
    (Sharpness.expectationJ (withGhost G) β J A * Sharpness.expectationJ (withGhost G) β J B)
        * (Sharpness.currentSum (withGhost G) β J ∅) ^ 2
      = Sharpness.currentSum (withGhost G) β J A * Sharpness.currentSum (withGhost G) β J B := by
  rw [gc10_eq15_ghost G β J A, gc10_eq15_ghost G β J B]; ring
















theorem gc10_correlationProduct_eq_sourcePairSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) (A B : Finset (Option V)) :
    (Sharpness.expectationJ (withGhost G) β J A * Sharpness.expectationJ (withGhost G) β J B)
        * (Sharpness.currentSum (withGhost G) β J ∅) ^ 2
      = Sharpness.sourcePairSum (withGhost G) β J A B := by
  rw [gc10_eq15_product_two_currentMass G β J A B,
      gc10_currentMass_product_eq_sourcePairSum G β J A B]












theorem gc10_sourcePairSum_superposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) (A B : Finset (Option V)) :
    Sharpness.sourcePairSum (withGhost G) β J A B
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ,
          ∑ K : {p : ↥(withGhost G).edgeFinset → ℕ // p ≤ m},
            (if sources (withGhost G) (ofEdgeFun (withGhost G) K.1) = A
                then weight (withGhost G) β J (ofEdgeFun (withGhost G) K.1) else 0)
              * (if sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K.1 e)) = B
                    then weight (withGhost G) β J (ofEdgeFun (withGhost G) (fun e => m e - K.1 e))
                    else 0) :=
  Sharpness.sourcePairSum_eq_superposition (withGhost G) β J A B











theorem gc10_eq15_currentMass_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    0 < Sharpness.currentSum (withGhost G) β J ∅ :=
  gc9_sourceless_pos (withGhost G) β J






theorem gc10_eq15_currentMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 (Option V) → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (A : Finset (Option V)) :
    0 ≤ Sharpness.currentSum (withGhost G) β J A
      ∧ 0 ≤ Sharpness.expectationJ (withGhost G) β J A :=
  ⟨gc9_currentSum_nonneg (withGhost G) β J hβ hJ A,
   gc9_expectationJ_nonneg (withGhost G) β J hβ hJ A⟩



















theorem gc10_eq15_magnetization (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (y : V) :
    Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb))
      = isingExpectation G β h (fun s => spin s y)
        * Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  rw [gc10_eq15_ghost (G := G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc6_ghostGraph_dictionary G β h y]












theorem gc10_eq15_nonvacuous (β : ℝ) (J : Sym2 (Option (Fin 4)) → ℝ) :
    (Sharpness.expectationJ (withGhost (⊥ : SimpleGraph (Fin 4))) β J
          ({some 1, some 2} : Finset (Option (Fin 4)))
        * Sharpness.expectationJ (withGhost (⊥ : SimpleGraph (Fin 4))) β J
            ({some 3, none} : Finset (Option (Fin 4))))
        * (Sharpness.currentSum (withGhost (⊥ : SimpleGraph (Fin 4))) β J ∅) ^ 2
      = Sharpness.sourcePairSum (withGhost (⊥ : SimpleGraph (Fin 4))) β J
          ({some 1, some 2} : Finset (Option (Fin 4))) ({some 3, none} : Finset (Option (Fin 4))) :=
  gc10_correlationProduct_eq_sourcePairSum (⊥ : SimpleGraph (Fin 4)) β J
    ({some 1, some 2} : Finset (Option (Fin 4))) ({some 3, none} : Finset (Option (Fin 4)))

end StatMech.Walls
