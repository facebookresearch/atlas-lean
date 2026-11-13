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
import Code.Walls.gc6_ghostgraph
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












theorem gc10_ghostEdge_coupling_eq_field (h β : ℝ) (x : V) :
    ghostCoupling h β (fun _ => 1) s(some x, none) = h :=
  rfl










theorem gc10_ghost_bondSum_absorbs_field (β h : ℝ) (s : ConfigSpace (Option V)) :
    (∑ e ∈ (withGhost G).edgeFinset, ghostCoupling h β (fun _ => 1) e * bond s e)
      = (∑ e ∈ G.edgeFinset, (fun _ : Sym2 V => (1 : ℝ)) e * bond s (Sym2.map some e))
        + h * spin s none * ∑ x : V, spin s (some x) :=
  ghost_bondSum G h β (fun _ => 1) s











theorem gc10_ghostEdge_encodes_field (β h : ℝ) (s : ConfigSpace (Option V)) :
    boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s
      = isingWeight G β (h * spin s none) (fun z => s (some z)) :=
  fgd_ghost_weight_eq G β h s













theorem gc10_ghostPaired_card_even (A : Finset V) (hA : Odd A.card) :
    Even ((insert (none : Option V) (A.map someEmb)).card) := by
  have hmem : (none : Option V) ∉ A.map someEmb := by simp [Finset.mem_map, someEmb]
  rw [Finset.card_insert_of_notMem hmem, Finset.card_map]
  exact Odd.add_one hA








theorem gc10_ghostPaired_observable (a : V) (s : ConfigSpace (Option V)) :
    spinProd (insert (none : Option V) (({a} : Finset V).map someEmb)) s
      = spin s (some a) * spin s none := by
  rw [gc6_spinProd_insert_ghost_factor]
  have hmap : spinProd (({a} : Finset V).map someEmb) s = spin s (some a) := by
    unfold spinProd
    rw [show (({a} : Finset V).map someEmb) = ({some a} : Finset (Option V)) from by
      ext z; simp [someEmb]]
    rw [Finset.prod_singleton]
  rw [hmap]; ring

















theorem gc10_magnetisation_dictionary (β h : ℝ) (a : V) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({a} : Finset V).map someEmb))
      = isingExpectation G β h (fun s => spin s a) :=
  gc6_ghostGraph_dictionary G β h a











theorem gc10_magnetisation_dictionary_explicit (β h : ℝ) (a : V) :
    isingExpectation G β h (fun s => spin s a)
      = (∑ s : ConfigSpace (Option V),
            (spin s (some a) * spin s none)
              * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s)
          / partitionJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) :=
  gc6_ghostGraph_dictionary_explicit G β h a









theorem gc10_magnetisation_dictionary_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (A.map someEmb))
      = isingExpectation G β h (spinProd A) :=
  gc6_expectationJ_ghost_odd G β h A hA














theorem gc10_ghost_Z0_pos (β h : ℝ) :
    0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  gc5_Z0_pos (withGhost G) β (ghostCoupling h β (fun _ => 1))














theorem gc10_magnetisation_currentRatio (β h : ℝ) (a : V) :
    isingExpectation G β h (fun s => spin s a)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({a} : Finset V).map someEmb))
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  gc6_ghostGraph_currentRatio G β h a









theorem gc10_magnetisation_currentRatio_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    isingExpectation G β h (spinProd A)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (A.map someEmb))
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  gc6_ghostGraph_currentRatio_odd G β h A hA




































theorem gc10_ghostDictionary (β h : ℝ) (a : V) :
    
    ((∀ x : V, ghostCoupling h β (fun _ => 1) s(some x, none) = h)
        ∧ (∀ s : ConfigSpace (Option V),
            boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s
              = isingWeight G β (h * spin s none) (fun z => s (some z))))
    
    ∧ (expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({a} : Finset V).map someEmb))
        = isingExpectation G β h (fun s => spin s a))
    
    ∧ (isingExpectation G β h (fun s => spin s a)
          = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({a} : Finset V).map someEmb))
              / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
  refine ⟨⟨fun x => gc10_ghostEdge_coupling_eq_field h β x,
          fun s => gc10_ghostEdge_encodes_field G β h s⟩,
        gc10_magnetisation_dictionary G β h a,
        gc10_magnetisation_currentRatio G β h a,
        gc10_ghost_Z0_pos G β h⟩










theorem gc10_ghostDictionary_nonvacuous :
    ((∀ x : Fin 3, ghostCoupling (1 : ℝ) 1 (fun _ => 1) s(some x, none) = 1)
        ∧ (∀ s : ConfigSpace (Option (Fin 3)),
            boltzmannJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) s
              = isingWeight (⊤ : SimpleGraph (Fin 3)) 1 (1 * spin s none) (fun z => s (some z))))
    ∧ (expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
          (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb))
        = isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0))
    ∧ (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (fun s => spin s 0)
          = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
                (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb))
              / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅)
    ∧ (0 < currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅) :=
  gc10_ghostDictionary (⊤ : SimpleGraph (Fin 3)) 1 1 0




theorem gc10_ghostPaired_card_even_nonvacuous :
    Even ((insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)).card) :=
  gc10_ghostPaired_card_even (V := Fin 3) ({0} : Finset (Fin 3)) (by simp)

end StatMech.Walls
