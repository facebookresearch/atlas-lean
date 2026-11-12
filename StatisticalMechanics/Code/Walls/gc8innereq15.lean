/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Ising.CorrelationRatio
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

























theorem gc8_inner_eq15 (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (y g : V) :
    Sharpness.currentSum S β J ({y, g} : Finset V)
      = Sharpness.expectationJ S β J ({y, g} : Finset V) * Sharpness.currentSum S β J ∅ :=
  acr_eq15_insertion' S β J ({y, g} : Finset V)













theorem gc8_inner_eq15_ratio_nonneg (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) :
    0 ≤ Sharpness.expectationJ S β J ({y, g} : Finset V) :=
  acr_expectationJ_nonneg S β J hβ hJ ({y, g} : Finset V)





theorem gc8_inner_eq15_sourceless_pos (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) :
    0 < Sharpness.currentSum S β J ∅ :=
  acr_currentSum_empty_pos S β J





theorem gc8_inner_eq15_lhs_nonneg (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) :
    0 ≤ Sharpness.currentSum S β J ({y, g} : Finset V) :=
  acr_currentSum_nonneg S β J hβ hJ ({y, g} : Finset V)

















theorem gc8_inner_eq15_sq (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (y g : V) :
    Sharpness.expectationJ S β J ({y, g} : Finset V) * Sharpness.currentSum S β J ({y, g} : Finset V)
      = (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ :=
  acr_eq15_insertion_sq S β J ({y, g} : Finset V)
    (ne_of_gt (gc8_inner_eq15_sourceless_pos S β J))
























theorem gc8_inner_eq15_claim1_step (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) (eΛ : ℝ)
    (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
    eΛ * Sharpness.currentSum S β J ({y, g} : Finset V)
      ≥ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ := by
  rw [gc8_inner_eq15 S β J y g]
  exact acr_claim1_griffiths_step (Sharpness.expectationJ S β J ({y, g} : Finset V))
    (Sharpness.currentSum S β J ∅) eΛ
    (gc8_inner_eq15_ratio_nonneg S β J hβ hJ y g)
    (gc8_inner_eq15_sourceless_pos S β J).le hgriff




















theorem gc8_inner_eq15_ghost_magnetization (S : SimpleGraph V) [DecidableRel S.Adj] (β h : ℝ)
    (y : V) :
    expectationJ (withGhost S) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb))
      = isingExpectation S β h (fun s => spin s y) :=
  gc6_ghostGraph_dictionary S β h y











theorem gc8_inner_eq15_magnetization (S : SimpleGraph V) [DecidableRel S.Adj] (β h : ℝ) (y : V) :
    Sharpness.currentSum (withGhost S) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb))
      = isingExpectation S β h (fun s => spin s y)
        * Sharpness.currentSum (withGhost S) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  rw [acr_eq15_insertion' (withGhost S) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc8_inner_eq15_ghost_magnetization S β h y]











theorem gc8_inner_eq15_nonvacuous (β : ℝ) (J : Sym2 (Fin 4) → ℝ) :
    Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4))
      = Sharpness.expectationJ (⊥ : SimpleGraph (Fin 4)) β J ({1, 2} : Finset (Fin 4))
        * Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) β J ∅ :=
  gc8_inner_eq15 (⊥ : SimpleGraph (Fin 4)) β J 1 2

end StatMech.Walls
