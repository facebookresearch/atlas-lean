/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.OSSS.RevealmentCrossBox
import Code.OSSS.ReachDomination

open scoped BigOperators
open StatMech.Lattice

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.DecisionTree
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.TreeComplete
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]

















theorem oc_crosstree_query_incident (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
    (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
  
  
  have hInv0 : geomInv endU endV ω B ((disc₀, (∅ : Finset V)) : XState V).1 :=
    fun x hx => connOpenSet_of_mem (hdisc₀ x hx)
  
  
  
  obtain ⟨τ, hτInv, hτg⟩ :=
    mem_queried_buildTree (guard := xbGuard endU endV)
      (step := xbStep endU endV o)
      (base := fun s => decide (∃ y ∈ s.2, y ∈ C))
      (Inv := fun s => geomInv endU endV ω B s.1) (ω := ω)
      (fun σ e hσ hg => by
        
        
        have hg1 : geomGuard endU endV σ.1 e = true := hg
        have hstep := geomInv_step endU endV ω B σ.1 e hσ hg1
        rwa [← fst_xbStep endU endV o σ e (ω e)] at hstep)
      (repeatList l (xbCount endU endV o l disc₀)) (disc₀, ∅) hInv0 i hi
  
  
  have hτg' : geomGuard endU endV τ.1 i = true := hτg
  unfold geomGuard at hτg'
  simp only [decide_eq_true_eq] at hτg'
  rcases hτg' with hU | hV
  · exact Or.inl (hτInv _ hU)
  · exact Or.inr (hτInv _ hV)







theorem oc_crosstree_query_incident_eq_engine (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
    (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    oc_crosstree_query_incident endU endV o B C l disc₀ hdisc₀ ω i hi
      = StatMech.OSSS.queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hi :=
  rfl







theorem oc_incidentCluster_of_queried_crossTree (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
    (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    StatMech.OSSS.ReachDomination.IncidentCluster endU endV ω B i :=
  oc_crosstree_query_incident endU endV o B C l disc₀ hdisc₀ ω i hi

end Walls
end StatMech
