/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceOrbit
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.InterfaceConnectedGlobal
import Code.Lattice.InterfaceConnectedBuild
import Code.Lattice.ContourLinksExits
import Code.Lattice.ExitDartsOrbit

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}









def IsOrbitEdge (K : Set (Site 2)) (e : Dart) (x y : Site 2) : Prop :=
  ∃ d : Dart, SameOrbit K e d ∧
    ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x))


theorem obs_isOrbitEdge_symm (K : Set (Site 2)) (e : Dart) {x y : Site 2}
    (h : IsOrbitEdge K e x y) : IsOrbitEdge K e y x := by
  obtain ⟨d, hd, hc⟩ := h; exact ⟨d, hd, hc.symm⟩




noncomputable def latticeMinusOrbit (K : Set (Site 2)) (e : Dart) : SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ ¬ IsOrbitEdge K e x y
  symm := by
    intro x y ⟨hadj, hno⟩
    exact ⟨hadj.symm, fun h => hno (obs_isOrbitEdge_symm K e h)⟩
  loopless := ⟨fun _ h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem latticeMinusOrbit_adj (K : Set (Site 2)) (e : Dart) (x y : Site 2) :
    (latticeMinusOrbit K e).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ ¬ IsOrbitEdge K e x y := Iff.rfl









theorem obs_orbitEdge_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2} (h : IsOrbitEdge K e x y) :
    ∃ d : Dart, IsBoundaryDart K d ∧ SameOrbit K e d ∧
      ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x)) := by
  obtain ⟨d, hd, hcase⟩ := h
  obtain ⟨n, hn⟩ := hd
  have hbd : IsBoundaryDart K d := by rw [← hn]; exact iterate_isBoundaryDart' K e he n
  exact ⟨d, hbd, ⟨n, hn⟩, hcase⟩



theorem obs_orbitEdge_one_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : (x ∈ K ↔ y ∉ K) := by
  obtain ⟨d, hbd, _, hcase⟩ := obs_orbitEdge_isBoundaryDart K e he h
  rcases hcase with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · subst ht hh; exact ⟨fun _ => hbd.2, fun _ => hbd.1⟩
  · subst ht hh; exact ⟨fun hx => absurd hx hbd.2, fun hy => absurd hbd.1 hy⟩


theorem obs_not_orbitEdge_of_both_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (hx : x ∈ K) (hy : y ∈ K) : ¬ IsOrbitEdge K e x y := fun h =>
  (obs_orbitEdge_one_in_K K e he h).mp hx hy


theorem obs_not_orbitEdge_of_both_not_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (hx : x ∉ K) (hy : y ∉ K) : ¬ IsOrbitEdge K e x y := fun h => by
  have hiff := obs_orbitEdge_one_in_K K e he h
  exact hy (by by_contra hyk; exact hx (hiff.mpr hyk))










theorem obs_orbitReachable_of_complReachable (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (h : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩) :
    (latticeMinusOrbit K e).Reachable u w := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), ((hypercubicLattice 2).induce Kᶜ).Walk a b →
      (latticeMinusOrbit K e).Reachable (a : Site 2) (b : Site 2) from H ⟨u, hu⟩ ⟨w, hw⟩ p
  intro a b q
  induction q with
  | nil => exact Reachable.refl _
  | @cons a b c hadj q' ih =>
    have hadj' : (hypercubicLattice 2).Adj (a : Site 2) (b : Site 2) := hadj
    have hno : ¬ IsOrbitEdge K e (a : Site 2) (b : Site 2) :=
      obs_not_orbitEdge_of_both_not_in_K K e he a.2 b.2
    exact (SimpleGraph.Adj.reachable ((latticeMinusOrbit_adj K e _ _).mpr ⟨hadj', hno⟩)).trans ih






theorem obs_orbitReachable_of_connected (o : Site 2) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω o) e) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hxy : Connected 2 ω x y) :
    (latticeMinusOrbit (cluster 2 ω o) e).Reachable x y := by
  obtain ⟨p⟩ := hxy
  suffices H : ∀ (a b : Site 2), (openSubgraph 2 ω).Walk a b → a ∈ cluster 2 ω o →
      (latticeMinusOrbit (cluster 2 ω o) e).Reachable a b from H x y p hx
  intro a b q
  induction q with
  | nil => intro _; exact Reachable.refl _
  | @cons a b c hadj q' ih =>
    intro ha
    have hadjL : (hypercubicLattice 2).Adj a b := hadj.1
    have hab_open : Connected 2 ω a b := ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩
    have hb : b ∈ cluster 2 ω o := by rw [mem_cluster] at ha ⊢; exact ha.trans hab_open
    have hno : ¬ IsOrbitEdge (cluster 2 ω o) e a b :=
      obs_not_orbitEdge_of_both_in_K (cluster 2 ω o) e he ha hb
    exact
      (SimpleGraph.Adj.reachable ((latticeMinusOrbit_adj _ e _ _).mpr ⟨hadjL, hno⟩)).trans (ih hb)










theorem obs_sameOrbit_of_orbitEdge_boundary (K : Set (Site 2)) (e f : Dart)
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (h : IsOrbitEdge K e f.tail f.head) : SameOrbit K e f := by
  obtain ⟨d, hbd, hso, hcase⟩ := obs_orbitEdge_isBoundaryDart K e he h
  rcases hcase with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have heq : d = f := Dart.ext ht hh
    rwa [heq] at hso
  · exfalso
    have hdtail : d.tail ∈ K := hbd.1
    rw [ht] at hdtail
    exact hf.2 hdtail













def OrbitSeparates (K : Set (Site 2)) (e : Dart) : Prop :=
  ¬ (latticeMinusOrbit K e).Reachable e.tail e.head










theorem obs_traceSurjective_of_orbitSeparates (o : Site 2)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
    OrbitTraceSurjective (cluster 2 ω o) := by
  intro e f he hf hreach
  set K := cluster 2 ω o with hK
  
  have hReachTail : (latticeMinusOrbit K e).Reachable e.tail f.tail := by
    have h1 : (latticeMinusOrbit K e).Reachable o e.tail :=
      obs_orbitReachable_of_connected o e he (self_mem_cluster ω o) he.1
    have h2 : (latticeMinusOrbit K e).Reachable o f.tail :=
      obs_orbitReachable_of_connected o e he (self_mem_cluster ω o) hf.1
    exact h1.symm.trans h2
  
  have hReachHead : (latticeMinusOrbit K e).Reachable e.head f.head :=
    obs_orbitReachable_of_complReachable K e he he.2 hf.2 hreach
  
  have hsepe : ¬ (latticeMinusOrbit K e).Reachable e.tail e.head := hsep e he
  by_cases hOE : IsOrbitEdge K e f.tail f.head
  · exact obs_sameOrbit_of_orbitEdge_boundary K e f he hf hOE
  · 
    exfalso
    have hadjLMO : (latticeMinusOrbit K e).Adj f.tail f.head :=
      (latticeMinusOrbit_adj K e _ _).mpr ⟨f.adj, hOE⟩
    exact hsepe ((hReachTail.trans hadjLMO.reachable).trans hReachHead.symm)




theorem obs_interfaceConnected_of_orbitSeparates (o : Site 2)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
    InterfaceConnected (cluster 2 ω o) :=
  (orbitTraceSurjective_iff_interfaceConnected (cluster 2 ω o)).mp
    (obs_traceSurjective_of_orbitSeparates o hsep)











def OrbitCoversBoundaryEdges (K : Set (Site 2)) (e : Dart) : Prop :=
  ∀ {x y : Site 2}, (hypercubicLattice 2).Adj x y → bdEdge K s(x, y) → IsOrbitEdge K e x y



theorem obs_latticeMinusOrbit_le_barrier (K : Set (Site 2)) (e : Dart)
    (hcov : OrbitCoversBoundaryEdges K e) :
    latticeMinusOrbit K e ≤ latticeMinusBarrier K := by
  intro x y h
  obtain ⟨hadj, hno⟩ := h
  exact ⟨hadj, fun hbd => hno (hcov hadj hbd)⟩





theorem obs_orbitSeparates_of_coversBoundary (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e := by
  intro hreach
  have hbarrier : (latticeMinusBarrier K).Reachable e.tail e.head :=
    hreach.mono (obs_latticeMinusOrbit_le_barrier K e hcov)
  exact not_reachable_latticeMinusBarrier K he.1 he.2 hbarrier











theorem obs_orbitCoversBoundaryEdges_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    OrbitCoversBoundaryEdges ({c} : Set (Site 2)) e := by
  intro x y hadj hbd
  rw [bdEdge_mk] at hbd
  simp only [Set.mem_singleton_iff] at hbd
  by_cases hx : x = c
  · have hy : y ≠ c := by have := hbd.mp hx; simpa using this
    have hadjcy : (hypercubicLattice 2).Adj c y := by rw [← hx]; exact hadj
    refine ⟨⟨c, y, hadjcy⟩, ?_, Or.inl ⟨hx.symm, rfl⟩⟩
    exact ifc_singleton_sameOrbit c e ⟨c, y, hadjcy⟩ he
      ⟨Set.mem_singleton _, by simpa using hy⟩
  · have hy : y = c := by
      by_contra hyne
      exact hx (hbd.mpr hyne)
    have hadjcx : (hypercubicLattice 2).Adj c x := by rw [← hy]; exact hadj.symm
    refine ⟨⟨c, x, hadjcx⟩, ?_, Or.inr ⟨hy.symm, rfl⟩⟩
    exact ifc_singleton_sameOrbit c e ⟨c, x, hadjcx⟩ he
      ⟨Set.mem_singleton _, by simpa using hx⟩




theorem obs_orbitSeparates_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    OrbitSeparates ({c} : Set (Site 2)) e :=
  obs_orbitSeparates_of_coversBoundary ({c} : Set (Site 2)) e he
    (obs_orbitCoversBoundaryEdges_singleton c e he)













theorem obs_exitDartsSameOrbit_of_orbitSeparates (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω (origin 2)) e →
        OrbitSeparates (cluster 2 ω (origin 2)) e)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  icb_exitDartsSameOrbit_of_traceSurjective (ω := ω) hfin
    (obs_traceSurjective_of_orbitSeparates (origin 2) hsep) R hR hr hl







theorem obs_pc_lt_one_of_orbitSeparates_and_links
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  pc_lt_one_via_dartOrbit h




































end Lattice

end StatMech
