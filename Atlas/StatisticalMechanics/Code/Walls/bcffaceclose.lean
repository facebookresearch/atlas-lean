/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Walls.fwrfaceregion
import Code.Walls.bc69count

open Set SimpleGraph Finset
open scoped BigOperators
open StatMech StatMech.Lattice

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {d : ℕ}















theorem bcf_forest_no_contour {V : Type*} {G : SimpleGraph V} (hac : G.IsAcyclic)
    {v : V} (c : G.Walk v v) : ¬ c.IsCycle := hac c






theorem bcf_acyclic_cycle_absurd {V : Type*} {G : SimpleGraph V} (hac : G.IsAcyclic)
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) : False := hac c hc





theorem bcf_cycle_three_le_length {V : Type*} {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) : 3 ≤ c.length :=
  hc.three_le_length
















theorem bcf_no_forest_contour_for_faceCut {a : Site 2}
    {G : SimpleGraph (Site 2)} (hGle : G ≤ hypercubicLattice 2) (hGac : G.IsAcyclic)
    (Vc : (hypercubicLattice 2).Walk a a) (hcyc : Vc.IsCycle)
    (hedges : ∀ e ∈ Vc.edges, e ∈ G.edgeSet) : False := by
  classical
  
  have hmem : ∀ e ∈ Vc.edges, e ∈ G.edgeSet := hedges
  have htr : (Vc.transfer G hmem).IsCycle := hcyc.transfer hmem
  exact hGac _ htr















theorem bcf_vertexBoundary_is_site_shell (d R : ℕ) :
    vertexBoundary d R = box d R \ box d (R - 1) := rfl




theorem bcf_faceCut_is_edgeSet (T : Site 2 → Prop) :
    jed_cutSet T = {e : Sym2 (Site 2) | ∃ a b : Site 2, (hypercubicLattice 2).Adj a b ∧
      e = sharedPrimalEdge a b ∧ (T a ↔ ¬ T b)} := rfl









































theorem bcf_status :
    
    (∀ {V : Type} {G : SimpleGraph V}, G.IsAcyclic → ∀ {v : V} (c : G.Walk v v), ¬ c.IsCycle) ∧
    
    (∀ {V : Type} {G : SimpleGraph V} {v : V} {c : G.Walk v v}, c.IsCycle → 3 ≤ c.length) ∧
    
    (∀ {a : Site 2} {G : SimpleGraph (Site 2)}, G ≤ hypercubicLattice 2 → G.IsAcyclic →
      ∀ (Vc : (hypercubicLattice 2).Walk a a), Vc.IsCycle →
        (∀ e ∈ Vc.edges, e ∈ G.edgeSet) → False) ∧
    
    (∀ (d R : ℕ), vertexBoundary d R = box d R \ box d (R - 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V G hac v c; exact bcf_forest_no_contour hac c
  · intro V G v c hc; exact bcf_cycle_three_le_length hc
  · intro a G hle hac Vc hcyc hedges; exact bcf_no_forest_contour_for_faceCut hle hac Vc hcyc hedges
  · intro d R; exact bcf_vertexBoundary_is_site_shell d R

end StatMech.Walls
