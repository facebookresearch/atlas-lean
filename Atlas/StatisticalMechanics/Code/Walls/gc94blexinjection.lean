/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.gc88brereroutehall
import Code.Walls.gc89bmetricinjection
import Code.Walls.gc90bperfiberinject
import Code.Walls.gc91bglobalinjection
import Code.Walls.gc92borbitobstruction

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]















def gc94b_dropReroute (P : Finset ι → Finset ι) (s : Finset ι × Finset ι) : Finset ι × Finset ι :=
  (s.1 \ P s.1, s.2)


def gc94b_stashReroute (P : Finset ι → Finset ι) (s : Finset ι × Finset ι) : Finset ι × Finset ι :=
  (s.1 \ P s.1, s.2 ∆ P s.1)













theorem gc94b_lexPath_breaks_symmetry :
    
    ({1} : Finset (Fin 4)) ≠ ({2} : Finset (Fin 4))
    
      ∧ ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4)) := by
  refine ⟨by decide, by decide⟩











theorem gc94b_lexReroute_collides_wred :
    gc94b_dropReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∧ gc94b_dropReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      
      ∧ gc94b_dropReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = gc94b_dropReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) := by
  refine ⟨by decide, by decide, by decide⟩












theorem gc94b_lexStash_fails_to_land_wred :
    
    gc94b_stashReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), ({1} : Finset (Fin 4)))
      ∧ gc94b_stashReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), ({2} : Finset (Fin 4)))
      ∧ gc94b_stashReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        ≠ gc94b_stashReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
    
      ∧ sources gc88b_wredEnds ({1} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4))
      ∧ sources gc88b_wredEnds ({2} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4))
      ∧ ({0, 3} : Finset (Fin 4)) ≠ (∅ : Finset (Fin 4)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩




theorem gc94b_lexStash_not_in_T3 :
    ((∅ : Finset (Fin 4)), ({1} : Finset (Fin 4)))
        ∉ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3
      ∧ ((∅ : Finset (Fin 4)), ({2} : Finset (Fin 4)))
        ∉ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
  constructor <;>
  · intro h
    simp only [gc91b_T3Pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at h
    
    have := h.2.2.2.1
    revert this
    decide












theorem gc94b_sourceFree_classification (K : Finset (Fin 4)) :
    sources gc88b_wredEnds K = (∅ : Finset (Fin 4))
      ↔ (K = (∅ : Finset (Fin 4)) ∨ K = ({1, 2} : Finset (Fin 4))) := by
  revert K; decide






theorem gc94b_sourceFree_swapFixed_wred (K : Finset (Fin 4))
    (hK : sources gc88b_wredEnds K = (∅ : Finset (Fin 4))) :
    K.image (Equiv.swap (1 : Fin 4) 2) = K := by
  rcases (gc94b_sourceFree_classification K).1 hK with rfl | rfl
  · decide
  · decide





theorem gc94b_all_T3_swapFixed (JJ : Finset (Fin 4) × Finset (Fin 4))
    (hJJ : JJ ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) :
    gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) JJ = JJ := by
  simp only [gc91b_T3Pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hJJ
  obtain ⟨_, _, hJ1, hJ2, _⟩ := hJJ
  unfold gc92b_pairAction
  rw [gc94b_sourceFree_swapFixed_wred JJ.1 hJ1, gc94b_sourceFree_swapFixed_wred JJ.2 hJ2]














theorem gc94b_rankMatch_is_circular (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    Nonempty ({KK // KK ∈ gc91b_cogxgPairs ends m o x g}
        ↪ {JJ // JJ ∈ gc91b_T3Pairs ends m o x y g})
      ↔ gc87b_CogxgLeT3 ends m o x y g :=
  gc91b_boundary_marriage_iff ends m hnd hxg





















theorem gc94b_lex_status :
    
    (({1} : Finset (Fin 4)) ≠ ({2} : Finset (Fin 4))
        ∧ ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4)))
    
    ∧ gc94b_dropReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = gc94b_dropReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
    
    ∧ (gc94b_stashReroute (fun K => K) (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
          ≠ gc94b_stashReroute (fun K => K) (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        ∧ ((∅ : Finset (Fin 4)), ({1} : Finset (Fin 4)))
            ∉ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3)
    
    ∧ (∀ JJ ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3,
        gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) JJ = JJ) := by
  refine ⟨gc94b_lexPath_breaks_symmetry, gc94b_lexReroute_collides_wred.2.2, ?_,
      fun JJ hJJ => gc94b_all_T3_swapFixed JJ hJJ⟩
  · exact ⟨gc94b_lexStash_fails_to_land_wred.2.2.1, gc94b_lexStash_not_in_T3.1⟩






















theorem gc94b_machine_findings : True := trivial

end StatMech.Walls
