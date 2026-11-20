/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.FieldGhostDict
import Code.Ising.CorrelationRatio
import Code.Walls.gc5_ergrep
import Code.Walls.gc6_ghostgraph
import Code.Walls.gc7core
import Code.Walls.gc6_core

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





















theorem gc8_Z0_pos (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    0 < Sharpness.currentSum (withGhost G) β J ∅ :=
  acr_currentSum_empty_pos (withGhost G) β J











theorem gc8_Z0_pos_ghost (β h : ℝ) :
    0 < Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  gc8_Z0_pos G β (ghostCoupling h β (fun _ => 1))



theorem gc8_Z0_ne_zero (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    Sharpness.currentSum (withGhost G) β J ∅ ≠ 0 :=
  ne_of_gt (gc8_Z0_pos G β J)



theorem gc8_Z0_ne_zero_ghost (β h : ℝ) :
    Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0 :=
  ne_of_gt (gc8_Z0_pos_ghost G β h)
















theorem gc8_Z0_eq_partition_over_pow (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    Sharpness.currentSum (withGhost G) β J ∅
      = Sharpness.partitionJ (withGhost G) β J / (2 : ℝ) ^ (Fintype.card (Option V)) := by
  have h := Sharpness.partitionJ_eq_currentSum (withGhost G) β J
  have h2 : (2 : ℝ) ^ (Fintype.card (Option V)) ≠ 0 := by positivity
  rw [h, mul_comm, mul_div_assoc, div_self h2, mul_one]


















theorem gc8_ghostRatio_well_defined (β h : ℝ) (a : V) :
    isingExpectation G β h (fun s => spin s a)
        = Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({a} : Finset V).map someEmb))
            / Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅
      ∧ 0 < Sharpness.currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  ⟨gc6_ghostGraph_currentRatio G β h a, gc8_Z0_pos_ghost G β h⟩

















theorem gc8_eq15_insertion_ghost (β : ℝ) (J : Sym2 (Option V) → ℝ) (A : Finset (Option V)) :
    Sharpness.currentSum (withGhost G) β J A
      = Sharpness.expectationJ (withGhost G) β J A
          * Sharpness.currentSum (withGhost G) β J ∅ :=
  acr_eq15_insertion (withGhost G) β J A (gc8_Z0_ne_zero G β J)



















theorem gc8_claim1_griffiths_step_ghost (β : ℝ) (J : Sym2 (Option V) → ℝ) (A : Finset (Option V))
    (eΛ : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
    eΛ * Sharpness.currentSum (withGhost G) β J A
      ≥ (Sharpness.expectationJ (withGhost G) β J A) ^ 2
          * Sharpness.currentSum (withGhost G) β J ∅ := by
  rw [gc8_eq15_insertion_ghost G β J A]
  exact acr_claim1_griffiths_step (Sharpness.expectationJ (withGhost G) β J A)
    (Sharpness.currentSum (withGhost G) β J ∅) eΛ
    (acr_expectationJ_nonneg (withGhost G) β J hβ hJ A)
    (acr_currentSum_nonneg (withGhost G) β J hβ hJ ∅) hgriff




















theorem gc8_u3_nonpos_of_eqSwi (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc6_core_ursell_nonpos G β h hβ hh o hid x y









theorem gc8_Z0_pos_nonvacuous :
    0 < Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
          (ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  gc8_Z0_pos_ghost (⊤ : SimpleGraph (Fin 3)) 1 1




theorem gc8_ghostRatio_well_defined_nonvacuous :
    isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0)
        = Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
              (ghostCoupling 1 1 (fun _ => 1))
              (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb))
            / Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
                (ghostCoupling 1 1 (fun _ => 1)) ∅
      ∧ 0 < Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
              (ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  gc8_ghostRatio_well_defined (⊤ : SimpleGraph (Fin 3)) 1 1 0

end StatMech.Walls
