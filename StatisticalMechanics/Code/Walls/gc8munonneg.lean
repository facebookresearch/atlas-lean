/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Ising.CorrelationRatio

open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]












theorem gc8_mu_nonneg (GΛ : SimpleGraph V) [DecidableRel GΛ.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y g : V) :
    0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) :=
  gks_first GΛ β h hβ hh _











theorem gc8_magY_nonneg (GΛ : SimpleGraph V) [DecidableRel GΛ.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (y : V) :
    0 ≤ isingExpectation GΛ β h (spinProd ({y} : Finset V)) :=
  gks_first GΛ β h hβ hh _




theorem gc8_magYsq_nonneg (GΛ : SimpleGraph V) [DecidableRel GΛ.Adj] (β h : ℝ) (y : V) :
    0 ≤ (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2 := by positivity





theorem gc8_twoPoint_nonneg (GS : SimpleGraph V) [DecidableRel GS.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (hh : 0 ≤ h) (o x : V) :
    0 ≤ isingExpectation GS β h (spinProd ({o, x} : Finset V)) :=
  gks_first GS β h hβ hh _













theorem gc8_normaliser_nonneg (GΛ GS : SimpleGraph V) [DecidableRel GΛ.Adj] [DecidableRel GS.Adj]
    (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y g : V) :
    0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))
        * (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2
        * isingExpectation GS β h (spinProd ({o, x} : Finset V)) := by
  have hμ := gc8_mu_nonneg GΛ β h hβ hh o x y g
  have hox := gc8_twoPoint_nonneg GS β h hβ hh o x
  positivity






















theorem gc8_claim1_griffiths_step (GΛ GS : SimpleGraph V) [DecidableRel GΛ.Adj] [DecidableRel GS.Adj]
    (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y g : V)
    (hgriff : isingExpectation GS β h (spinProd ({y} : Finset V))
              ≤ isingExpectation GΛ β h (spinProd ({y} : Finset V))) :
    isingExpectation GΛ β h (spinProd ({y} : Finset V))
        * (isingExpectation GS β h (spinProd ({y} : Finset V))
            * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)))
      ≥ (isingExpectation GS β h (spinProd ({y} : Finset V))) ^ 2
          * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) :=
  acr_claim1_griffiths_step _ _ _
    (gc8_magY_nonneg GS β h hβ hh y)
    (gc8_mu_nonneg GΛ β h hβ hh o x y g)
    hgriff











theorem gc8_claim1_normaliser_lower_bound (GΛ GS : SimpleGraph V) [DecidableRel GΛ.Adj]
    [DecidableRel GS.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y g : V)
    (hgriff : isingExpectation GS β h (spinProd ({y} : Finset V))
              ≤ isingExpectation GΛ β h (spinProd ({y} : Finset V))) :
    isingExpectation GS β h (spinProd ({o, x} : Finset V))
        * (isingExpectation GΛ β h (spinProd ({y} : Finset V))
            * (isingExpectation GS β h (spinProd ({y} : Finset V))
                * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))))
      ≥ isingExpectation GS β h (spinProd ({o, x} : Finset V))
          * ((isingExpectation GS β h (spinProd ({y} : Finset V))) ^ 2
              * isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))) := by
  rw [ge_iff_le]
  exact mul_le_mul_of_nonneg_left
    (gc8_claim1_griffiths_step GΛ GS β h hβ hh o x y g hgriff)
    (gc8_twoPoint_nonneg GS β h hβ hh o x)
















theorem gc8_twoPoint_ge_product (GS : SimpleGraph V) [DecidableRel GS.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    isingExpectation GS β h (spinProd ({o} : Finset V))
        * isingExpectation GS β h (spinProd ({x} : Finset V))
      ≤ isingExpectation GS β h (spinProd ({o, x} : Finset V)) := by
  have h2 := gks_second GS β h hβ hh ({o} : Finset V) ({x} : Finset V)
  have hsymm : ({o} : Finset V) ∆ ({x} : Finset V) = ({o, x} : Finset V) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hox⟩
      · exact Or.inr ⟨rfl, fun h => hox h.symm⟩
  rwa [hsymm] at h2












theorem gc8_mu_clause (GΛ : SimpleGraph V) [DecidableRel GΛ.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y g : V) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ = isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)) :=
  ⟨isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V)),
    gc8_mu_nonneg GΛ β h hβ hh o x y g, rfl⟩










theorem gc8_mu_nonneg_nonvacuous :
    0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2} : Finset (Fin 3))) :=
  gks_first (⊤ : SimpleGraph (Fin 3)) 1 1 (by norm_num) (by norm_num) _




theorem gc8_normaliser_nonneg_nonvacuous :
    0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2, 0} : Finset (Fin 3)))
        * (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({2} : Finset (Fin 3)))) ^ 2
        * isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) :=
  gc8_normaliser_nonneg (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3)) 1 1
    (by norm_num) (by norm_num) 0 1 2 0

end StatMech.Walls
