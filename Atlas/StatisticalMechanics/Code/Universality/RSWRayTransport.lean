/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWOuterStraddle



















open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



theorem rlc_oppositeLoopSides_iff_leftRegion_xor
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a) (x y : Site 2) :
    rlc_OppositeLoopSides C x y ↔
      (x ∈ jec_leftRegion C ∧ y ∉ jec_leftRegion C) ∨
        (x ∉ jec_leftRegion C ∧ y ∈ jec_leftRegion C) := by
  simp only [rlc_OppositeLoopSides, jec_mem_leftRegion]
  tauto



theorem rlc_not_oppositeLoopSides_of_both_mem_leftRegion
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∈ jec_leftRegion C) (hy : y ∈ jec_leftRegion C) :
    ¬ rlc_OppositeLoopSides C x y := by
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor]
  tauto



theorem rlc_not_oppositeLoopSides_of_both_not_mem_leftRegion
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∉ jec_leftRegion C) (hy : y ∉ jec_leftRegion C) :
    ¬ rlc_OppositeLoopSides C x y := by
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor]
  tauto




def rlc_primalDualReflectFun (x : Site 2) : Site 2 := ![-x 0, x 1 + 1]


def rlc_primalDualReflectInvFun (x : Site 2) : Site 2 := ![-x 0, x 1 - 1]



def rlc_primalDualReflect : Site 2 ≃ Site 2 where
  toFun := rlc_primalDualReflectFun
  invFun := rlc_primalDualReflectInvFun
  left_inv x := by
    ext i
    fin_cases i <;> simp [rlc_primalDualReflectFun,
      rlc_primalDualReflectInvFun]
  right_inv x := by
    ext i
    fin_cases i <;> simp [rlc_primalDualReflectFun,
      rlc_primalDualReflectInvFun]

@[simp] theorem rlc_primalDualReflect_zero (x : Site 2) :
    rlc_primalDualReflect x 0 = -x 0 := by
  rfl

@[simp] theorem rlc_primalDualReflect_one (x : Site 2) :
    rlc_primalDualReflect x 1 = x 1 + 1 := by
  rfl

@[simp] theorem rlc_primalDualReflect_symm_zero (x : Site 2) :
    rlc_primalDualReflect.symm x 0 = -x 0 := by
  rfl

@[simp] theorem rlc_primalDualReflect_symm_one (x : Site 2) :
    rlc_primalDualReflect.symm x 1 = x 1 - 1 := by
  rfl



noncomputable def rlc_dualReflectLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := rlc_dualReflect
  map_rel' := fun {x y} hxy => (rlc_adj_dualReflect x y).mp hxy



theorem rlc_rayEdge_dualReflect_iff {z u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v) :
    jec_rayEdge (rlc_primalDualReflect z)
        s(rlc_dualReflect u, rlc_dualReflect v) ↔
      bdEdge (jec_belowSet (z 1)) s(u, v) ∧
        ¬ jec_rayEdge z s(u, v) := by
  rw [jec_rayEdge_mk, jec_belowSet_bdEdge (z 1) u v hadj,
    jec_rayEdge_mk]
  simp only [rlc_primalDualReflect_zero, rlc_primalDualReflect_one,
    rlc_dualReflect_zero, rlc_dualReflect_one]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  omega

private theorem rlc_countP_complement_within
    {E : Type*} (l : List E) (P Q : E → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hsub : ∀ e ∈ l, P e → Q e) :
    l.countP (fun e => decide (Q e ∧ ¬ P e)) +
        l.countP (fun e => decide (P e)) =
      l.countP (fun e => decide (Q e)) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      have hesub : P e → Q e := hsub e (by simp)
      have hlsub : ∀ f ∈ l, P f → Q f := by
        intro f hf
        exact hsub f (by simp [hf])
      specialize ih hlsub
      simp only [List.countP_cons]
      by_cases hP : P e <;> by_cases hQ : Q e <;> simp_all <;> omega





theorem rlc_rayParity_dualReflect_map {a : Site 2}
    (w : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    Even (jec_rayCount (rlc_primalDualReflect z)
      (w.map rlc_dualReflectLatticeHom)) ↔
      Even (jec_rayCount z w) := by
  classical
  have hcount :
      jec_rayCount (rlc_primalDualReflect z)
          (w.map rlc_dualReflectLatticeHom) + jec_rayCount z w =
        crossCount (jec_belowSet (z 1)) w := by
    rw [jec_rayCount, SimpleGraph.Walk.edges_map, List.countP_map,
      jec_rayCount, crossCount]
    change
      w.edges.countP (fun e => decide
          (jec_rayEdge (rlc_primalDualReflect z)
            (Sym2.map rlc_dualReflectLatticeHom e))) +
        w.edges.countP (fun e => decide (jec_rayEdge z e)) =
      w.edges.countP (fun e => decide
        (bdEdge (jec_belowSet (z 1)) e))
    have hreflect :
        w.edges.countP (fun e => decide
          (jec_rayEdge (rlc_primalDualReflect z)
            (Sym2.map rlc_dualReflectLatticeHom e))) =
        w.edges.countP (fun e => decide
          (bdEdge (jec_belowSet (z 1)) e ∧ ¬ jec_rayEdge z e)) := by
      apply List.countP_congr
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v =>
          simp only [Sym2.map_mk, decide_eq_true_eq]
          exact rlc_rayEdge_dualReflect_iff (w.adj_of_mem_edges he)
    rw [hreflect]
    exact rlc_countP_complement_within w.edges
      (jec_rayEdge z) (bdEdge (jec_belowSet (z 1))) (by
        intro e he hray
        induction e using Sym2.inductionOn with
        | _ u v =>
            have hadj := w.adj_of_mem_edges he
            rw [jec_rayEdge_mk] at hray
            rw [jec_belowSet_bdEdge (z 1) u v hadj]
            exact ⟨hray.1.1, hray.2⟩)
  have htotal : Even (crossCount (jec_belowSet (z 1)) w) :=
    crossCount_even_of_loop (jec_belowSet (z 1)) w
  rw [← hcount] at htotal
  exact Nat.even_add.mp htotal


def rlc_reflectedPrimalRegion (K : Set (Site 2)) : Set (Site 2) :=
  rlc_primalDualReflect '' K

@[simp] theorem rlc_mem_reflectedPrimalRegion_iff
    (K : Set (Site 2)) (x : Site 2) :
    x ∈ rlc_reflectedPrimalRegion K ↔
      rlc_primalDualReflect.symm x ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨rlc_primalDualReflect.symm x, hx, by simp⟩



def RlcReflectedEndpointXor {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (K : Set (Site 2)) : Prop :=
  (((gamma.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K) ≠
      ((gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K)) ∧
    (((gamma'.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K) ≠
      ((gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K))




theorem rlc_endpointSides_of_reflectedRegion_xor
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a)
    (K : Set (Site 2))
    (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C)
    (hxor : RlcReflectedEndpointXor gamma gamma' K) :
    rlc_OppositeLoopSides C
        (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2) ∧
      rlc_OppositeLoopSides C
        (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2) := by
  constructor
  · rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion]
    rcases hxor with ⟨hxor, _⟩
    by_cases hstart : (gamma.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
    · by_cases hend : (gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact False.elim (hxor (propext ⟨fun _ => hend, fun _ => hstart⟩))
      · exact Or.inl ⟨hstart, hend⟩
    · by_cases hend : (gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact Or.inr ⟨hstart, hend⟩
      · exact False.elim (hxor (propext ⟨fun h => False.elim (hstart h),
          fun h => False.elim (hend h)⟩))
  · rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion]
    rcases hxor with ⟨_, hxor⟩
    by_cases hstart : (gamma'.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
    · by_cases hend : (gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact False.elim (hxor (propext ⟨fun _ => hend, fun _ => hstart⟩))
      · exact Or.inl ⟨hstart, hend⟩
    · by_cases hend : (gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact Or.inr ⟨hstart, hend⟩
      · exact False.elim (hxor (propext ⟨fun h => False.elim (hstart h),
          fun h => False.elim (hend h)⟩))





theorem rlc_outerExitEndpointSides_of_reflectedRegion_xor
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hregion : rlc_reflectedPrimalRegion
        (rlc_mixedWiredReachSet G omega) =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)))
    (hxor : RlcReflectedEndpointXor gamma gamma'
      (rlc_mixedWiredReachSet G omega)) :
    RlcOuterExitEndpointSides G hn hlt omega := by
  exact rlc_endpointSides_of_reflectedRegion_xor _ _ hregion hxor




theorem rlc_outerExitGoodContactPair_of_endpointSides
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hsides : RlcOuterExitEndpointSides G hn hlt omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    Nonempty (RlcOuterExitGoodContactPair G omega) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitAnchor G omega)
  let q := rlc_outerExitReflectedOpenLoop G hn hlt omega
  obtain ⟨hright, hleft⟩ :=
    rlc_outerExit_both_straddles_of_endpointSides G hn hlt omega hsides
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hright hleft
  have hqSupport : q.support = List.map rlc_dualReflect c.support := by
    simp [q, c, rlc_outerExitReflectedOpenLoop,
      rlc_dualReflectOpenWalk, SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_mapLe_eq_support, rlc_dualReflectOpenHom]
  rw [hqSupport] at hxrQ hyrQ
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hxrQ
  obtain ⟨y, hy, hyr⟩ := List.mem_map.mp hyrQ
  have hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
    simpa using hxr ▸ hxrPath
  have hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
    simpa using hyr ▸ hyrPath
  exact ⟨RlcOuterExitGoodContactPair.ofContactOrder
    horder hx hy hxPath hyPath⟩



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_reflectedRegion_xor
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hregion : rlc_reflectedPrimalRegion
        (rlc_mixedWiredReachSet G omega) =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)))
    (hxor : RlcReflectedEndpointXor gamma gamma'
      (rlc_mixedWiredReachSet G omega))
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  have hsides : RlcOuterExitEndpointSides G hn hlt omega :=
    rlc_outerExitEndpointSides_of_reflectedRegion_xor
      G hn hlt omega hregion hxor
  have hcontacts : Nonempty (RlcOuterExitGoodContactPair G omega) :=
    rlc_outerExitGoodContactPair_of_endpointSides
      G hn hlt omega hsides horder
  obtain ⟨hcontacts⟩ := hcontacts
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair
    G hn hlt omega hcontacts




theorem rlc_not_outerExitEndpointSides_of_failure_of_directRegionEq
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hregion : rlc_mixedWiredReachSet G omega =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _))) :
    ¬ RlcOuterExitEndpointSides G hn hlt omega := by
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  obtain ⟨hr0, hr1, hl0, hl1⟩ :=
    rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure G omega hno
  intro hsides
  have hr0' : (gamma.1.1 : Site 2) ∈ jec_leftRegion C := by
    rw [← hregion]
    exact hr0
  have hr1' : (gamma.1.2.1 : Site 2) ∈ jec_leftRegion C := by
    rw [← hregion]
    exact hr1
  exact (rlc_not_oppositeLoopSides_of_both_mem_leftRegion C hr0' hr1')
    hsides.1

end Universality
end StatMech
