/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Lattice.JordanEnclosureDuality
import Code.Lattice.OrbitWindingWitness
import Code.Walls.kwceventtocut

open SimpleGraph Set

namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable













def jbw_bdEdgeSet (S : Set (Site 2)) : Set (Sym2 (Site 2)) := {e | bdEdge S e}

@[simp] theorem jbw_mem_bdEdgeSet (S : Set (Site 2)) (e : Sym2 (Site 2)) :
    e ∈ jbw_bdEdgeSet S ↔ bdEdge S e := Iff.rfl


















def jbw_singleton : Set (Site 2) := {origin 2}







theorem jbw_vertexCut_not_even :
    ¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0]) := by
  classical
  have hdeg : jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0] = 1 := by
    rw [jce_degree]
    have hset : (Finset.univ.filter
        (fun i : Fin 4 => s(![(1 : ℤ), 0], jce_nbr ![(1 : ℤ), 0] i)
          ∈ jbw_bdEdgeSet jbw_singleton)) = {1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        jbw_mem_bdEdgeSet, bdEdge_mk, jbw_singleton, Set.mem_singleton_iff, jce_nbr,
        origin_eq_zerozero]
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, site2_eq, Fin.isValue,
          Fin.ext_iff, Fin.val_one] <;> first | omega | tauto
    rw [hset]; rfl
  rw [hdeg]; decide

















theorem jbw_jed_reachability (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    H.Reachable p q :=
  jed_reachable_of_separated H hfin p q f0 g0 hpq hnpq hfg hshared hsep











theorem jbw_easyHalf {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd






def jbw_hard_gap {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    s(u, v) ∈ Vc.edges.toFinset → bdEdge (jec_leftRegion Vc) s(u, v)






theorem jbw_hardGap_iff_windingBody {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (jbw_hard_gap Vc ∧
      ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges.toFinset)
    ↔ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))) := by
  constructor
  · rintro ⟨hf, hb⟩ u v hadj
    exact ⟨fun h => hf hadj h, fun h => hb hadj h⟩
  · intro h
    exact ⟨fun hadj he => (h hadj).mp he, fun hadj hb => (h hadj).mpr hb⟩





theorem jbw_hard_gap_of_windingMatch (hmatch : kwc_PrimalWalkLeftRegionMatch)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : jbw_hard_gap Vc := by
  intro u v hadj he
  exact (hmatch Vc hadj).mp he





























theorem jbw_jed_insufficient :
    
    (¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0])) ∧
    
    (∀ (H : SimpleGraph (Site 2)), H.edgeSet.Finite → ∀ (p q f0 g0 : Site 2),
        (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
        (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
        ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 → H.Reachable p q) ∧
    
    (kwc_PrimalWalkLeftRegionMatch →
      ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc) :=
  ⟨jbw_vertexCut_not_even, jbw_jed_reachability, fun h _ Vc => jbw_hard_gap_of_windingMatch h Vc⟩

end Walls

end StatMech
