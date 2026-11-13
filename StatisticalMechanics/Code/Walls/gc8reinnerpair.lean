/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Mathlib
import Code.Ising.CorrelationRatio
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Walls.gc6_ghostgraph

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


















theorem gc8r_reinner_pair_eq15sq (GS : SimpleGraph V) [DecidableRel GS.Adj] (β : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) (h0 : Sharpness.currentSum GS β J ∅ ≠ 0) :
    Sharpness.expectationJ GS β J A * Sharpness.currentSum GS β J A
      = (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅ :=
  Ising.acr_eq15_insertion_sq GS β J A h0
























theorem gc8r_reinner_pair (GS : SimpleGraph V) [DecidableRel GS.Adj] (β : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) (hc : 0 < Sharpness.currentSum GS β J ∅) :
    (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅
      = (Sharpness.currentSum GS β J A) ^ 2 / Sharpness.currentSum GS β J ∅ := by
  have hne : Sharpness.currentSum GS β J ∅ ≠ 0 := ne_of_gt hc
  
  have hratio : Sharpness.currentSum GS β J A
      = Sharpness.expectationJ GS β J A * Sharpness.currentSum GS β J ∅ :=
    Ising.acr_eq15_insertion GS β J A hne
  rw [hratio]
  field_simp









theorem gc8r_reinner_pair_unconditional (GS : SimpleGraph V) [DecidableRel GS.Adj] (β : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) :
    (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅
      = (Sharpness.currentSum GS β J A) ^ 2 / Sharpness.currentSum GS β J ∅ :=
  gc8r_reinner_pair GS β J A (Ising.acr_currentSum_empty_pos GS β J)










theorem gc8r_reinner_pair_mul (GS : SimpleGraph V) [DecidableRel GS.Adj] (β : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) :
    ((Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅)
        * Sharpness.currentSum GS β J ∅
      = (Sharpness.currentSum GS β J A) ^ 2 := by
  have hne : Sharpness.currentSum GS β J ∅ ≠ 0 :=
    ne_of_gt (Ising.acr_currentSum_empty_pos GS β J)
  have hratio : Sharpness.currentSum GS β J A
      = Sharpness.expectationJ GS β J A * Sharpness.currentSum GS β J ∅ :=
    Ising.acr_eq15_insertion GS β J A hne
  rw [hratio]; ring















theorem gc8r_squared_mass_nonneg (GS : SimpleGraph V) [DecidableRel GS.Adj] (β : ℝ)
    (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    0 ≤ (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅ :=
  mul_nonneg (sq_nonneg _) (Ising.acr_currentSum_nonneg GS β J hβ hJ ∅)
























theorem gc8r_reinner_pair_ghost (GS : SimpleGraph V) [DecidableRel GS.Adj] (β h : ℝ) (y : V) :
    (isingExpectation GS β h (fun s => spin s y)) ^ 2
        * currentSum (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1)) ∅
      = (currentSum (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({y} : Finset V).map FieldGhostDict.someEmb))) ^ 2
          / currentSum (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1)) ∅ := by
  
  have hdict : isingExpectation GS β h (fun s => spin s y)
      = Sharpness.expectationJ (withGhost GS) β (FieldGhostDict.ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({y} : Finset V).map FieldGhostDict.someEmb)) :=
    (gc6_ergRep_ghost_compat GS β h y)
  rw [hdict]
  exact gc8r_reinner_pair_unconditional (withGhost GS) β
    (FieldGhostDict.ghostCoupling h β (fun _ => 1))
    (insert (none : Option V) (({y} : Finset V).map FieldGhostDict.someEmb))





















theorem gc8r_reinner_pair_griffiths_chain (GS : SimpleGraph V) [DecidableRel GS.Adj] (β : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) (eΛ : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hgriff : Sharpness.expectationJ GS β J A ≤ eΛ) :
    eΛ * Sharpness.currentSum GS β J A
      ≥ (Sharpness.currentSum GS β J A) ^ 2 / Sharpness.currentSum GS β J ∅ := by
  have hc : 0 < Sharpness.currentSum GS β J ∅ := Ising.acr_currentSum_empty_pos GS β J
  have hne : Sharpness.currentSum GS β J ∅ ≠ 0 := ne_of_gt hc
  
  have hratio : Sharpness.currentSum GS β J A
      = Sharpness.expectationJ GS β J A * Sharpness.currentSum GS β J ∅ :=
    Ising.acr_eq15_insertion GS β J A hne
  
  have hstep := Ising.acr_claim1_griffiths_step (Sharpness.expectationJ GS β J A)
    (Sharpness.currentSum GS β J ∅) eΛ
    (Ising.acr_expectationJ_nonneg GS β J hβ hJ A)
    (Ising.acr_currentSum_nonneg GS β J hβ hJ ∅) hgriff
  
  have hrepair := gc8r_reinner_pair GS β J A hc
  rw [ge_iff_le, ← hrepair]
  calc (Sharpness.expectationJ GS β J A) ^ 2 * Sharpness.currentSum GS β J ∅
      ≤ eΛ * (Sharpness.expectationJ GS β J A * Sharpness.currentSum GS β J ∅) := hstep
    _ = eΛ * Sharpness.currentSum GS β J A := by rw [← hratio]










theorem gc8r_reinner_pair_nonvacuous :
    (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0)) ^ 2
        * currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
            (FieldGhostDict.ghostCoupling 1 1 (fun _ => 1)) ∅
      = (currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
            (FieldGhostDict.ghostCoupling 1 1 (fun _ => 1))
            (insert (none : Option (Fin 3))
              (({0} : Finset (Fin 3)).map FieldGhostDict.someEmb))) ^ 2
          / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
              (FieldGhostDict.ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  gc8r_reinner_pair_ghost (⊤ : SimpleGraph (Fin 3)) 1 1 0

end StatMech.Walls
