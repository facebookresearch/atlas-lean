/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanEnclosureDuality
import Code.Lattice.PeierlsSingleCircuit
import Code.Walls.fwrfaceregion

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech
namespace Walls
open StatMech.Lattice

attribute [local instance] Classical.propDecidable











def pcf_faceCutGraph (T : Site 2 → Prop) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ (T f ↔ ¬ T g)
  symm := by
    intro f g ⟨hadj, hsplit⟩
    refine ⟨hadj.symm, ?_⟩
    by_cases hf : T f <;> by_cases hg : T g <;> simp_all
  loopless := by
    refine ⟨fun f h => ?_⟩
    exact (hypercubicLattice 2).irrefl h.1

@[simp] theorem pcf_faceCutGraph_adj (T : Site 2 → Prop) (f g : Site 2) :
    (pcf_faceCutGraph T).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ (T f ↔ ¬ T g) := Iff.rfl


theorem pcf_faceCutGraph_le (T : Site 2 → Prop) :
    pcf_faceCutGraph T ≤ hypercubicLattice 2 := fun _ _ h => h.1


noncomputable instance pcf_instLocallyFinite (T : Site 2 → Prop) :
    SimpleGraph.LocallyFinite (pcf_faceCutGraph T) := by
  classical
  exact fun f =>
    Fintype.ofFinset
      ((candFinset 2 f).filter (fun g => (pcf_faceCutGraph T).Adj f g)) (by
        intro g
        rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        exact mem_candFinset_of_adj 2 f g (pcf_faceCutGraph_le T h))


theorem pcf_neighborFinset (T : Site 2 → Prop) (f : Site 2) :
    (pcf_faceCutGraph T).neighborFinset f =
      (candFinset 2 f).filter (fun g => (pcf_faceCutGraph T).Adj f g) := by
  classical
  apply Finset.ext
  intro g
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  refine ⟨fun h => ⟨mem_candFinset_of_adj 2 f g (pcf_faceCutGraph_le T h), h⟩, fun h => h.2⟩




theorem pcf_faceCutGraph_edge_iff_cutSet (T : Site 2 → Prop) {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    (pcf_faceCutGraph T).Adj f g ↔ sharedPrimalEdge f g ∈ jed_cutSet T := by
  rw [pcf_faceCutGraph_adj, jed_mem_cutSet_iff T hfg]
  exact and_iff_right hfg














theorem pcf_faceCutGraph_of_simpleCycle {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hnd : Vc.edges.Nodup) {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    (pcf_faceCutGraph (fwr_faceInside Vc)).Adj f g ↔ sharedPrimalEdge f g ∈ Vc.edges := by
  rw [pcf_faceCutGraph_edge_iff_cutSet (fwr_faceInside Vc) hfg]
  exact fwr_jedCutSet_match_of_nodup Vc hnd hfg

















theorem pcf_faceCutGraph_face_degree_not_even :
    ¬ (∀ (T : Site 2 → Prop) (f : Site 2), Even ((pcf_faceCutGraph T).degree f)) := by
  intro hall
  classical
  
  set T : Site 2 → Prop := fun f => f 0 ≤ 0 with hT
  
  have hnbr : (pcf_faceCutGraph T).neighborFinset (![(0:ℤ), 0]) = {![(1:ℤ), 0]} := by
    rw [pcf_neighborFinset, candFinset_face]
    apply Finset.ext
    intro g
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hadj, hsplit⟩
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
      simp only [hT, Matrix.cons_val_zero] at hsplit
      have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
      by_cases h00 : g 0 = 1
      · by_cases h01 : g 1 = 0
        · rw [hg, h00, h01]
        · exfalso; simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hadj; omega
      · exfalso
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hadj
        have hg0 : g 0 ≤ 0 := by omega
        exact absurd hg0 (by simpa using hsplit.mp (by omega))
    · rintro rfl
      refine ⟨by simp, latAdj_right 0 0, ?_⟩
      simp only [hT, Matrix.cons_val_zero]; omega
  have hdeg : (pcf_faceCutGraph T).degree (![(0:ℤ), 0]) = 1 := by
    rw [SimpleGraph.degree, hnbr, Finset.card_singleton]
  have := hall T (![(0:ℤ), 0])
  rw [hdeg] at this
  exact (Nat.not_even_one) this














theorem pcf_evenDegree_not_connectivity :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      (∀ v, Even (G.degree v)) ∧ ¬ G.Connected := by
  classical
  refine ⟨Fin 2, inferInstance, (⊥ : SimpleGraph (Fin 2)), inferInstance, ?_, ?_⟩
  · intro v
    have : (⊥ : SimpleGraph (Fin 2)).degree v = 0 := by
      rw [SimpleGraph.degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      exact (SimpleGraph.bot_adj _ _).mp hw
    rw [this]; exact Even.zero
  · intro hconn
    have := hconn.preconnected (0 : Fin 2) (1 : Fin 2)
    obtain ⟨w⟩ := this
    
    cases w with
    | cons hadj _ => exact (SimpleGraph.bot_adj _ _).mp hadj













theorem pcf_single_dualCircuit_of_connected {K : Set (Site 2)} (hK : K.Finite)
    (hconn : FaceBoundaryConnected K (boundarySupport hK))
    {f₀ : Site 2} (hf₀ : f₀ ∈ (boundarySupport hK : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph K).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges :=
  exists_single_dualCircuit_of_connected hK hconn hf₀

end Walls
end StatMech
