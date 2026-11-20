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
import Code.Sharpness.Switching
import Code.Walls.gc5_ergrep
import Code.Walls.gc6_ghostgraph
import Code.Walls.gc6_pairingpath

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














theorem gc7_edge_card_two (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    #(Finset.univ.filter (fun x : V => x ∈ e)) = 2 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := e.exists_rep
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  have hne : a ≠ b := he.ne
  rw [show (Finset.univ.filter (fun x : V => x ∈ s(a, b))) = {a, b} from ?_]
  · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  · ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
      Finset.mem_insert, Finset.mem_singleton]









theorem gc7_sum_incidentFlux_even (n : Sharpness.Current V) :
    Even (∑ x : V, Sharpness.incidentFlux G n x) := by
  have heq : (∑ x : V, Sharpness.incidentFlux G n x) = ∑ e ∈ G.edgeFinset, 2 * n e := by
    unfold Sharpness.incidentFlux
    rw [Finset.sum_comm']
    · refine Finset.sum_congr rfl (fun e he => ?_)
      rw [Finset.sum_const, smul_eq_mul, gc7_edge_card_two G e he]
    · intro x e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
  rw [heq]
  exact Finset.even_sum _ (fun e _ => ⟨n e, by ring⟩)










theorem gc7_sources_card_even (n : Sharpness.Current V) :
    Even (sources G n).card := by
  have hcount := (RandomCurrent.even_sum_iff_even_count (Finset.univ : Finset V)
    (fun x => Sharpness.incidentFlux G n x)).1 (gc7_sum_incidentFlux_even G n)
  rwa [show (Finset.univ.filter (fun x => Odd (Sharpness.incidentFlux G n x))) = sources G n
    from rfl] at hcount












theorem gc7_triple_card_odd (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Odd (({o, x, y} : Finset V).card) := by
  have hcard3 : (({o, x, y} : Finset V).card) = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  rw [hcard3]; decide






theorem gc7_combined_source_card (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card = 4 := by
  have hcard3 : (({o, x, y} : Finset V).card) = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  rw [Finset.card_insert_of_notMem (by simp [someEmb]), Finset.card_map, hcard3]





theorem gc7_combined_source_even (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
  rw [gc7_combined_source_card o x y hox hoy hxy]; decide




















theorem gc7_ghostEven_dictionary (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    isingExpectation G β h (spinProd ({o, x, y} : Finset V))
      = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) :=
  (gc6_expectationJ_ghost_odd G β h ({o, x, y} : Finset V)
    (gc7_triple_card_odd o x y hox hoy hxy)).symm





















theorem gc7_ghostEven_currentRatio (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    isingExpectation G β h (spinProd ({o, x, y} : Finset V))
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  gc6_ghostGraph_currentRatio_odd G β h ({o, x, y} : Finset V)
    (gc7_triple_card_odd o x y hox hoy hxy)







theorem gc7_representing_current_sources_even (m : Sharpness.Current (Option V))
    (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hm : sources (withGhost G) m = insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) :
    Even (sources (withGhost G) m).card
      ∧ Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
  refine ⟨gc7_sources_card_even (withGhost G) m, ?_⟩
  rw [gc7_combined_source_card o x y hox hoy hxy]; decide

















theorem gc7_ghostEven (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card
      ∧ isingExpectation G β h (spinProd ({o, x, y} : Finset V))
          = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
      ∧ isingExpectation G β h (spinProd ({o, x, y} : Finset V))
          = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
              / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  ⟨gc7_combined_source_even o x y hox hoy hxy,
   gc7_ghostEven_dictionary G β h o x y hox hoy hxy,
   gc7_ghostEven_currentRatio G β h o x y hox hoy hxy⟩








theorem gc7_combined_source_even_nonvacuous :
    Even (insert (none : Option (Fin 3))
      (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card :=
  gc7_combined_source_even (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)



theorem gc7_ghostEven_nonvacuous :
    Even (insert (none : Option (Fin 3))
        (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card
      ∧ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2} : Finset (Fin 3)))
          = expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
              (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb))
      ∧ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2} : Finset (Fin 3)))
          = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
                (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb))
              / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  gc7_ghostEven (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 (by decide) (by decide) (by decide)

end StatMech.Walls
