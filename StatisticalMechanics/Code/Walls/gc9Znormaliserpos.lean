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
import Code.Walls.gc8Z0pos
import Code.Walls.gc8core

open Finset BigOperators SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


















noncomputable def gc9_Z_normaliser (β : ℝ) (J : Sym2 (Option V) → ℝ) : ℝ :=
  (Sharpness.currentSum (withGhost G) β J ∅) ^ 2





















theorem gc9_Z_normaliser_pos (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    0 < gc9_Z_normaliser G β J := by
  have h := gc8_Z0_pos G β J
  unfold gc9_Z_normaliser
  positivity










theorem gc9_Z_normaliser_pos_ghost (β h : ℝ) :
    0 < gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) :=
  gc9_Z_normaliser_pos G β (ghostCoupling h β (fun _ => 1))




theorem gc9_Z_normaliser_ne_zero (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    gc9_Z_normaliser G β J ≠ 0 :=
  ne_of_gt (gc9_Z_normaliser_pos G β J)




theorem gc9_Z_normaliser_ne_zero_ghost (β h : ℝ) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) ≠ 0 :=
  ne_of_gt (gc9_Z_normaliser_pos_ghost G β h)















theorem gc9_Z_normaliser_two_current (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    gc9_Z_normaliser G β J
      = Sharpness.currentSum (withGhost G) β J ∅ * Sharpness.currentSum (withGhost G) β J ∅ := by
  unfold gc9_Z_normaliser; ring















theorem gc9_Z_normaliser_eq_partition_sq (β : ℝ) (J : Sym2 (Option V) → ℝ) :
    gc9_Z_normaliser G β J
      = (Sharpness.partitionJ (withGhost G) β J / (2 : ℝ) ^ (Fintype.card (Option V))) ^ 2 := by
  unfold gc9_Z_normaliser
  rw [gc8_Z0_eq_partition_over_pow]
















theorem gc9_Z_normaliser_instantiates_bridge (β h : ℝ) (J : Sym2 (Option V) → ℝ) (o x y : V)
    (D : ℝ) (hD : 0 ≤ D)
    (hid : eg_ursell3 G β h o x y * gc9_Z_normaliser G β J = -D) :
    ∃ (D' Z' : ℝ), (0 ≤ D') ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D' :=
  ⟨D, gc9_Z_normaliser G β J, hD, gc9_Z_normaliser_pos G β J, hid⟩









theorem gc9_Z_normaliser_pos_nonvacuous :
    0 < gc9_Z_normaliser (⊤ : SimpleGraph (Fin 3)) 1
          (ghostCoupling 1 1 (fun _ => 1)) :=
  gc9_Z_normaliser_pos_ghost (⊤ : SimpleGraph (Fin 3)) 1 1

end StatMech.Walls
