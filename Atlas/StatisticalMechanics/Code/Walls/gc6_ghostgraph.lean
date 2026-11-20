/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Ising.GKS
import Code.Sharpness.CurrentRep
import Code.Sharpness.RandomCurrent
import Code.Sharpness.FieldGhostDict
import Code.Walls.gc5_ergrep

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


















theorem gc6_num_neg_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s)
      = - ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV, isingWeight_flip, hA.neg_one_pow]
  ring








theorem gc6_spinProd_insert_ghost_factor (A : Finset V) (s : ConfigSpace (Option V)) :
    spinProd (insert (none : Option V) (A.map someEmb)) s
      = spin s none * spinProd (A.map someEmb) s := by
  have hmem : (none : Option V) ∉ A.map someEmb := by simp [Finset.mem_map, someEmb]
  unfold spinProd
  rw [Finset.prod_insert hmem]






theorem gc6_spinProd_insert_ghost_split (A : Finset V) (b : Bool) (τ : V → Bool) :
    spinProd (insert (none : Option V) (A.map someEmb))
        (fun a => Option.rec b τ a : Option V → Bool)
      = StatMech.Ising.spinB b * spinProd A τ := by
  have hmem : (none : Option V) ∉ A.map someEmb := by simp [Finset.mem_map, someEmb]
  unfold spinProd
  rw [Finset.prod_insert hmem]
  rw [show spin (fun a => Option.rec b τ a : Option V → Bool) none = StatMech.Ising.spinB b from rfl]
  congr 1
  rw [Finset.prod_map]
  rfl





















theorem gc6_num_ghost_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (insert (none : Option V) (A.map someEmb)) s
        * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s)
      = 2 * ∑ τ : ConfigSpace V, spinProd A τ * isingWeight G β h τ := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ τ : V → Bool, spinProd (insert (none : Option V) (A.map someEmb))
            (fun a => Option.rec b τ a)
          * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (fun a => Option.rec b τ a))
        = ∑ τ : V → Bool,
            StatMech.Ising.spinB b * spinProd A τ
              * isingWeight G β (h * StatMech.Ising.spinB b) τ := by
    intro b
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [fgd_ghost_weight_eq, split_ghost_spin, gc6_spinProd_insert_ghost_split]
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : StatMech.Ising.spinB false = -1 := rfl
  have htrue : StatMech.Ising.spinB true = 1 := rfl
  rw [htrue, hfalse]
  simp only [mul_one, one_mul, mul_neg, neg_mul]
  rw [show (∑ τ : V → Bool, -(spinProd A τ * isingWeight G β (-h) τ))
        = - ∑ τ : V → Bool, spinProd A τ * isingWeight G β (-h) τ from by
      rw [Finset.sum_neg_distrib]]
  rw [gc6_num_neg_odd G β h A hA]
  ring
















theorem gc6_expectationJ_ghost_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (A.map someEmb))
      = isingExpectation G β h (spinProd A) := by
  unfold expectationJ isingExpectation isingProb
  rw [fgd_partitionJ_ghost_eq]
  rw [gc6_num_ghost_odd G β h A hA]
  rw [show (∑ s : ConfigSpace V, isingWeight G β h s / isingZ G β h * spinProd A s)
        = (∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s) / isingZ G β h from by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun s _ => by ring)]
  rw [mul_comm (2 : ℝ), mul_div_assoc]
  rw [show (2 : ℝ) / (2 * isingZ G β h) = 1 / isingZ G β h from by
    rw [eq_div_iff (isingZ_ne_zero G β h)]
    field_simp
    rw [div_self (isingZ_ne_zero G β h)]]
  rw [mul_one_div]





















theorem gc6_ghostGraph_dictionary (β h : ℝ) (a : V) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({a} : Finset V).map someEmb))
      = isingExpectation G β h (fun s => spin s a) := by
  have hodd : Odd (({a} : Finset V).card) := by simp
  rw [gc6_expectationJ_ghost_odd G β h ({a} : Finset V) hodd]
  unfold isingExpectation spinProd
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.prod_singleton]











theorem gc6_ghostGraph_dictionary_explicit (β h : ℝ) (a : V) :
    isingExpectation G β h (fun s => spin s a)
      = (∑ s : ConfigSpace (Option V),
            (spin s (some a) * spin s none)
              * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s)
          / partitionJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) := by
  rw [← gc6_ghostGraph_dictionary G β h a]
  unfold expectationJ
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [gc6_spinProd_insert_ghost_factor]
  have hmap : spinProd (({a} : Finset V).map someEmb) s = spin s (some a) := by
    unfold spinProd
    rw [show (({a} : Finset V).map someEmb) = ({some a} : Finset (Option V)) from by
      ext z; simp [someEmb]]
    rw [Finset.prod_singleton]
  rw [hmap]; ring






















theorem gc6_ghostGraph_currentRatio_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    isingExpectation G β h (spinProd A)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (A.map someEmb))
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  rw [← gc6_expectationJ_ghost_odd G β h A hA, current_representation]











theorem gc6_ghostGraph_currentRatio (β h : ℝ) (a : V) :
    isingExpectation G β h (fun s => spin s a)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({a} : Finset V).map someEmb))
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  have hodd : Odd (({a} : Finset V).card) := by simp
  have h1 := gc6_ghostGraph_currentRatio_odd G β h ({a} : Finset V) hodd
  rw [show isingExpectation G β h (spinProd ({a} : Finset V))
        = isingExpectation G β h (fun s => spin s a) from by
      unfold isingExpectation spinProd
      exact Finset.sum_congr rfl (fun s _ => by rw [Finset.prod_singleton])] at h1
  exact h1






theorem gc6_ghost_Z0_pos (β h : ℝ) :
    0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  gc5_Z0_pos (withGhost G) β (ghostCoupling h β (fun _ => 1))






theorem gc6_ergRep_ghost_compat (β h : ℝ) (a : V) :
    isingExpectation G β h (fun s => spin s a)
      = Sharpness.expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({a} : Finset V).map someEmb)) := by
  rw [gc6_ghostGraph_dictionary]








theorem gc6_ghostGraph_dictionary_nonvacuous :
    expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1
        (ghostCoupling 1 1 (fun _ => 1))
        (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb))
      = isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0) :=
  gc6_ghostGraph_dictionary (⊤ : SimpleGraph (Fin 3)) 1 1 0


theorem gc6_ghostGraph_currentRatio_nonvacuous :
    isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0)
      = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
            (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb))
          / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  gc6_ghostGraph_currentRatio (⊤ : SimpleGraph (Fin 3)) 1 1 0

end StatMech.Walls
