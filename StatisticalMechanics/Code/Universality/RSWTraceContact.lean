/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















import Code.Universality.RSWLowestCrossing

open Function MeasureTheory Set

namespace StatMech

namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box


def rlc_OppositeLoopSides {a : Site 2}
    (C : (hypercubicLattice 2).Walk a a) (x y : Site 2) : Prop :=
  (Even (jec_rayCount x C) ∧ ¬ Even (jec_rayCount y C)) ∨
    (¬ Even (jec_rayCount x C) ∧ Even (jec_rayCount y C))





theorem rlc_closedLoop_contact_of_opposite_sides {a x y : Site 2}
    (C : (hypercubicLattice 2).Walk a a)
    (w : (hypercubicLattice 2).Walk x y)
    (hxy : rlc_OppositeLoopSides C x y) :
    ∃ z ∈ w.support, z ∈ C.support := by
  rcases hxy with hxy | hxy
  · obtain ⟨z, hz, hzC⟩ :=
      ccs_closedLoop_separatingSide_forces_cross C
        ({y} : Set (Site 2)) ({x} : Set (Site 2))
        (by simpa using hxy.2) (by simpa using hxy.1)
        (by simp) (by simp) w.reverse
    exact ⟨z, by simpa [SimpleGraph.Walk.support_reverse] using hz, hzC⟩
  · exact ccs_closedLoop_separatingSide_forces_cross C
      ({x} : Set (Site 2)) ({y} : Set (Site 2))
      (by simpa using hxy.1) (by simpa using hxy.2)
      (by simp) (by simp) w


noncomputable def rlc_ambientCrossingWalk {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) :
    (hypercubicLattice 2).Walk
      (gamma.1 : Site 2) (gamma.2.1 : Site 2) :=
  gamma.2.2.1.map
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom



theorem rlc_ambientCrossingWalk_support_mem_pathVertices
    {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) {z : Site 2}
    (hz : z ∈ (rlc_ambientCrossingWalk gamma).support) :
    z ∈ rlc_pathVertices gamma := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  have hzMapped : z ∈ List.map hom gamma.2.2.1.support := by
    have hsupp := SimpleGraph.Walk.support_map hom gamma.2.2.1
    have hm := congrArg (fun l => z ∈ l) hsupp
    exact Eq.mp hm (by simpa [rlc_ambientCrossingWalk, hom] using hz)
  rw [List.mem_map] at hzMapped
  obtain ⟨u, hu, huz⟩ := hzMapped
  change (u : Site 2) = z at huz
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨u, hu, huz⟩



theorem rlc_mem_ambientCrossingWalk_support_iff_pathVertices
    {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) (z : Site 2) :
    z ∈ (rlc_ambientCrossingWalk gamma).support ↔
      z ∈ rlc_pathVertices gamma := by
  constructor
  · exact rlc_ambientCrossingWalk_support_mem_pathVertices gamma
  · intro hz
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
        hypercubicLattice 2 :=
      (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
        (rect a b c d)).toHom
    have huMapped : (u : Site 2) ∈ List.map hom gamma.2.2.1.support :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    have hsupp := SimpleGraph.Walk.support_map hom gamma.2.2.1
    exact Eq.mpr (congrArg (fun l => (u : Site 2) ∈ l) hsupp) huMapped




def rlc_TraceStraddlesLoop {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d) : Prop :=
  ∃ x ∈ rlc_pathVertices gamma, ∃ y ∈ rlc_pathVertices gamma,
    rlc_OppositeLoopSides C x y




theorem rlc_closedLoop_contacts_crossingTrace_of_straddles
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d)
    (hstraddle : rlc_TraceStraddlesLoop C gamma) :
    ∃ z, z ∈ rlc_pathVertices gamma ∧ z ∈ C.support := by
  obtain ⟨x, hxPath, y, hyPath, hxy⟩ := hstraddle
  let W := rlc_ambientCrossingWalk gamma
  have hxW : x ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma x).2 hxPath
  have hyW : y ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma y).2 hyPath
  let wxy : (hypercubicLattice 2).Walk x y :=
    (W.takeUntil x hxW).reverse.append (W.takeUntil y hyW)
  obtain ⟨z, hzxy, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C wxy hxy
  have hzW : z ∈ W.support := by
    dsimp only [wxy] at hzxy
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hzxy
    rcases hzxy with hz | hz
    · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
    · exact W.support_takeUntil_subset_support hyW hz
  exact ⟨z,
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma z).1 hzW,
    hzC⟩



theorem rlc_closedLoop_contacts_both_wiredTraces_of_straddles {n : ℤ}
    {u : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_TraceStraddlesLoop C gamma.1)
    (hleft : rlc_TraceStraddlesLoop C gamma'.1) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ C.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ C.support) := by
  exact ⟨rlc_closedLoop_contacts_crossingTrace_of_straddles C gamma.1 hright,
    rlc_closedLoop_contacts_crossingTrace_of_straddles C gamma'.1 hleft⟩



theorem rlc_closedLoop_contacts_crossingTrace {a b c d : ℤ}
    {u : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d)
    (hsides : rlc_OppositeLoopSides C
      (gamma.1 : Site 2) (gamma.2.1 : Site 2)) :
    ∃ z, z ∈ rlc_pathVertices gamma ∧ z ∈ C.support := by
  obtain ⟨z, hzWalk, hzC⟩ :=
    rlc_closedLoop_contact_of_opposite_sides C
      (rlc_ambientCrossingWalk gamma) hsides
  exact ⟨z, rlc_ambientCrossingWalk_support_mem_pathVertices gamma hzWalk,
    hzC⟩





theorem rlc_closedLoop_contacts_both_wiredTraces {n : ℤ}
    {u : Site 2} (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_OppositeLoopSides C
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2))
    (hleft : rlc_OppositeLoopSides C
      (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ C.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ C.support) := by
  exact ⟨rlc_closedLoop_contacts_crossingTrace C gamma.1 hright,
    rlc_closedLoop_contacts_crossingTrace C gamma'.1 hleft⟩




def rlc_openSubgraph_le_lattice
    (eta : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 eta ≤ hypercubicLattice 2 :=
  fun _ _ h => h.1




theorem rlc_reflectedOpenDualCycle_contacts_both_of_straddles {n : ℤ}
    {eta : ConfigSpace (Sym2 (Site 2))} {u : Site 2}
    (c : (openSubgraph 2 eta).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_TraceStraddlesLoop
      (c.mapLe (rlc_openSubgraph_le_lattice eta)) gamma.1)
    (hleft : rlc_TraceStraddlesLoop
      (c.mapLe (rlc_openSubgraph_le_lattice eta)) gamma'.1) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ c.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ c.support) := by
  let C : (hypercubicLattice 2).Walk u u :=
    c.mapLe (rlc_openSubgraph_le_lattice eta)
  obtain ⟨⟨x, hxPath, hxC⟩, ⟨y, hyPath, hyC⟩⟩ :=
    rlc_closedLoop_contacts_both_wiredTraces_of_straddles
      C gamma gamma' hright hleft
  exact ⟨⟨x, hxPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hxC⟩,
    ⟨y, hyPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hyC⟩⟩




theorem rlc_reflectedOpenDualCycle_contacts_both_wiredTraces {n : ℤ}
    {eta : ConfigSpace (Sym2 (Site 2))} {u : Site 2}
    (c : (openSubgraph 2 eta).Walk u u)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hright : rlc_OppositeLoopSides
      (c.mapLe (rlc_openSubgraph_le_lattice eta))
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2))
    (hleft : rlc_OppositeLoopSides
      (c.mapLe (rlc_openSubgraph_le_lattice eta))
      (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) :
    (∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ c.support) ∧
      (∃ z, z ∈ rlc_pathVertices gamma'.1 ∧ z ∈ c.support) := by
  let C : (hypercubicLattice 2).Walk u u :=
    c.mapLe (rlc_openSubgraph_le_lattice eta)
  obtain ⟨⟨x, hxPath, hxC⟩, ⟨y, hyPath, hyC⟩⟩ :=
    rlc_closedLoop_contacts_both_wiredTraces C gamma gamma' hright hleft
  exact ⟨⟨x, hxPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hxC⟩,
    ⟨y, hyPath, by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hyC⟩⟩

end Universality

end StatMech
