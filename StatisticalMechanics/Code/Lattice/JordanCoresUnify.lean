/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.ArcSides
import Code.Lattice.Umlaufsatz
import Code.Lattice.InterfaceConnected
import Code.Lattice.DartOrbit
import Code.Lattice.OrbitEncloses

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.RSW.Box
open StatMech.Universality















theorem jcu_walk_crosses (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∉ S)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ e ∈ w.edges, bdEdge S e := by
  classical
  by_contra hcon
  push Not at hcon
  have h0 : crossCount S w = 0 := by
    rw [crossCount, List.countP_eq_zero]
    exact fun e he => by simp only [decide_eq_true_eq]; exact hcon e he
  exact (crossCount_odd_of_separated S hx hy w) (h0 ▸ Even.zero)








theorem jcu_walk_meets_innerBoundary (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∉ S)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ u v : Site 2, u ∈ w.support ∧ v ∈ w.support ∧
      (hypercubicLattice 2).Adj u v ∧ u ∈ S ∧ v ∉ S := by
  classical
  obtain ⟨e, hew, hbd⟩ := jcu_walk_crosses S hx hy w
  
  induction e with | _ a b =>
  have hadj : (hypercubicLattice 2).Adj a b := w.adj_of_mem_edges hew
  rw [bdEdge_mk] at hbd
  have ha : a ∈ w.support := w.fst_mem_support_of_mem_edges hew
  have hb : b ∈ w.support := w.snd_mem_support_of_mem_edges hew
  by_cases haS : a ∈ S
  · exact ⟨a, b, ha, hb, hadj, haS, hbd.mp haS⟩
  · 
    have hbS : b ∈ S := by by_contra hbS; exact haS (by tauto)
    exact ⟨b, a, hb, ha, hadj.symm, hbS, fun haS' => (hbd.mp haS') hbS⟩



























def jcu_HasSeparatingSide (D B inside outside : Set (Site 2)) : Prop :=
  ∃ S : Set (Site 2),
    (∀ z ∈ inside, z ∈ S) ∧
    (∀ z ∈ outside, z ∉ S) ∧
    (∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B))










theorem jcu_separatingSide_forces_cross {D B inside outside : Set (Site 2)}
    (h : jcu_HasSeparatingSide D B inside outside)
    {x y : Site 2} (hx : x ∈ inside) (hy : y ∈ outside)
    (w : (hypercubicLattice 2).Walk x y) (hwD : ∀ z ∈ w.support, z ∈ D) :
    ∃ z ∈ w.support, z ∈ B := by
  obtain ⟨S, hin, hout, hbd⟩ := h
  have hxS : x ∈ S := hin x hx
  have hyS : y ∉ S := hout y hy
  obtain ⟨u, v, hu, hv, hadj, huS, hvS⟩ := jcu_walk_meets_innerBoundary S hxS hyS w
  rcases hbd u v (hwD u hu) (hwD v hv) hadj huS hvS with hB | hB
  · exact ⟨u, hu, hB⟩
  · exact ⟨v, hv, hB⟩



















theorem jcu_floodFill_separatingSide (ω : ConfigSpace (Sym2 (Site 2)))
    (α β m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    {x y : Site 2} (hx : x ∈ rect α β c d) (hxα : x 0 = α)
    (hii : y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
    jcu_HasSeparatingSide (rect α β c d) (overlapComp ω m m' c d xB hxB) {x} {y} := by
  refine ⟨arcS_leftRegion ω α β m m' c d xB hxB, ?_, ?_, ?_⟩
  · 
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst z
    exact arcS_leftRegion_left ω α β m m' c d xB hxB x hx hxα
  · 
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst z; exact hii
  · 
    intro u v huD hvD hadj huS hvS
    apply arcS_leftRegion_bdEdge ω α β m m' c d xB hxB u v huD hvD hadj
    rw [bdEdge_mk]; exact ⟨fun _ => hvS, fun _ => huS⟩










theorem jcu_discreteJordan_imp_twoPathsCross (ω : ConfigSpace (Sym2 (Site 2)))
    (α β m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (hii : ∀ y : Site 2, y ∈ rect α β c d → y 0 = β →
      y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
    ArcS_TwoPathsCross ω α β m m' c d xB hxB := by
  intro _hαm _hmm' _hm'β x y hx hy hxα hyβ γ hsupp
  obtain ⟨z, hz, hzP⟩ :=
    jcu_separatingSide_forces_cross
      (jcu_floodFill_separatingSide ω α β m m' c d xB hxB hx hxα (hii y hy hyβ))
      rfl rfl γ hsupp
  exact ⟨z, hz, hzP⟩















theorem jcu_interface_separation (K : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ K) (hy : y ∉ K) (w : (hypercubicLattice 2).Walk x y) :
    ∃ e ∈ w.edges, bdEdge K e :=
  jcu_walk_crosses K hx hy w










theorem jcu_discreteJordan_imp_interfaceConnected (K : Set (Site 2))
    (htr : OrbitKingTransport K) (hcon : BoundaryKingConnected K)
    (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K :=
  interfaceConnected_of_kingResidues K htr hcon hsat































theorem jcu_discreteJordan_imp_orbitFaceNoPinch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hsimple : ∀ i ∈ Set.Iio (dartOrbitPeriod K a), ∀ j ∈ Set.Iio (dartOrbitPeriod K a),
      dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) →
        (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1) :
    OrbitFaceNoPinch K a := by
  intro i hi j hj hface
  
  rw [hsimple i hi j hj hface]







theorem jcu_orbitFaceNoPinch_imp_simple (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : OrbitFaceNoPinch K a)
    {i j : ℕ} (hi : i ∈ Set.Iio (dartOrbitPeriod K a)) (hj : j ∈ Set.Iio (dartOrbitPeriod K a))
    (hface : dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1)) :
    (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
  dartFace_eq_of_dir_eq (h i hi j hj hface) hface






theorem jcu_orbitFaceNoPinch_imp_injOn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : OrbitFaceNoPinch K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) :=
  orbitFace_injOn_of_noPinch K a h



























theorem jcu_twoPathsCross_of_floodFill_ii (ω : ConfigSpace (Sym2 (Site 2)))
    (α β m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (hii : ∀ y : Site 2, y ∈ rect α β c d → y 0 = β →
      y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
    ArcS_TwoPathsCross ω α β m m' c d xB hxB :=
  jcu_discreteJordan_imp_twoPathsCross ω α β m m' c d xB hxB hii

end Lattice

end StatMech
