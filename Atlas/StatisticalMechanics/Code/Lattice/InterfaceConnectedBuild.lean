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
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.PlanarTopology
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.LeftFace
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.BoundaryConnected
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceOrbit
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.InterfaceConnectedGlobal
import Code.Lattice.KingFacts
import Code.Lattice.ContourLinksExits
import Code.Lattice.ExitDartsOrbit
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}













theorem icb_orbitReached_straight_step (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d)
    (hfront : d.head + (-rot90Fun d.dir) ∉ K)
    (hside : d.tail + (-rot90Fun d.dir) ∈ K) :
    OrbitReached K e (d.head + (-rot90Fun d.dir)) := by
  refine ⟨dartNext K d, dartNext_isBoundaryDart K d hd, ?_, ?_⟩
  · exact dartNext_straight_head K d hfront hside
  · obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩






theorem icb_orbitReached_corner_step (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d)
    (hfront : d.head + (-rot90Fun d.dir) ∉ K)
    (hside : d.tail + (-rot90Fun d.dir) ∉ K) :
    OrbitReached K e (d.tail + (-rot90Fun d.dir)) := by
  refine ⟨dartNext K d, dartNext_isBoundaryDart K d hd, ?_, ?_⟩
  · exact dartNext_left_head K d hfront hside
  · obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩






theorem icb_orbitReached_wallStep (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d) :
    OrbitReached K e (dartNext K d).head ∧
      ((dartNext K d).head = d.head ∨ KingAdj d.head (dartNext K d).head) := by
  refine ⟨⟨dartNext K d, dartNext_isBoundaryDart K d hd, rfl, ?_⟩,
    kf_dartNext_head_kingAdj_or_eq K d⟩
  obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩













def UnitEdgeOrbitTransport (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e →
    ∀ {u v : Site 2} (_hu : u ∉ K) (_hv : v ∉ K),
      (hypercubicLattice 2).Adj u v →
      OrbitReached K e u → OrbitReached K e v






theorem icb_orbitReached_of_complReachable (K : Set (Site 2)) (htr : UnitEdgeOrbitTransport K)
    (e : Dart) (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩)
    (hou : OrbitReached K e u) : OrbitReached K e w := by
  obtain ⟨p⟩ := hreach
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), ((hypercubicLattice 2).induce Kᶜ).Walk a b →
      OrbitReached K e (a : Site 2) → OrbitReached K e (b : Site 2) from
    H ⟨u, hu⟩ ⟨w, hw⟩ p hou
  intro a b q
  induction q with
  | nil => intro h; exact h
  | @cons a b c hadj q' ih =>
    intro hoa
    have hadj' : (hypercubicLattice 2).Adj (a : Site 2) (b : Site 2) := hadj
    exact ih (htr e he a.2 b.2 hadj' hoa)





theorem icb_interfaceConnected_of_unitEdgeTransport (K : Set (Site 2))
    (htr : UnitEdgeOrbitTransport K) (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K := by
  intro e f he hf hreach
  have hbase : OrbitReached K e e.head := orbitReached_self K e he
  have hfhead : OrbitReached K e f.head :=
    icb_orbitReached_of_complReachable K htr e he he.2 hf.2 hreach hbase
  exact hsat e he hfhead f hf rfl













theorem icb_unitEdgeTransport_false :
    ¬ UnitEdgeOrbitTransport ({(0 : Site 2)} : Set (Site 2)) := by
  intro htr
  have hg : unitWt (![1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  set e : Dart := mkDart (0 : Site 2) (![1, 0] : Site 2) hg with he_def
  have hhead : e.head = (![1, 0] : Site 2) := by rw [he_def, mkDart_head]; simp
  have htail : e.tail = (0 : Site 2) := by rw [he_def, mkDart_tail]
  have hbd : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e := by
    refine ⟨by rw [htail]; exact Set.mem_singleton _, ?_⟩
    rw [hhead]; intro hc; simp only [Set.mem_singleton_iff] at hc
    have := congrFun hc 0; simp at this
  have hou : OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![1, 0] : Site 2) := by
    have := orbitReached_self ({(0 : Site 2)} : Set (Site 2)) e hbd; rwa [hhead] at this
  have hu : (![1, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hv : (![2, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hadj : (hypercubicLattice 2).Adj (![1, 0] : Site 2) (![2, 0] : Site 2) := by
    rw [adj_iff_unitWt_sub]
    show unitWt ((![1, 0] : Site 2) - (![2, 0] : Site 2)) = 1
    simp only [unitWt, Fin.sum_univ_two]; decide
  obtain ⟨d, hd, hdh, _⟩ := htr e hbd hu hv hadj hou
  
  have htaild : d.tail = (0 : Site 2) := by simpa using hd.1
  have hdir : d.dir = (![2, 0] : Site 2) := by rw [Dart.dir_def, hdh, htaild]; abel
  have hwt := unitWt_dir d
  rw [hdir] at hwt
  rw [show unitWt (![2, 0] : Site 2) = 2 by simp only [unitWt, Fin.sum_univ_two]; decide] at hwt
  exact absurd hwt (by decide)
















theorem icb_interfaceConnected_iff_traceSurjective (K : Set (Site 2)) :
    InterfaceConnected K ↔ OrbitTraceSurjective K :=
  (orbitTraceSurjective_iff_interfaceConnected K).symm



theorem icb_traceSurjective_singleton (c : Site 2) :
    OrbitTraceSurjective ({c} : Set (Site 2)) :=
  ifg_orbitTraceSurjective_singleton c





theorem icb_sameOrbit_imp_sameComponent (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) (h : SameOrbit K e f) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ :=
  sameComponent_of_sameOrbit K he hf h













theorem icb_exitHeads_reachable_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩
      ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩ := by
  have hkey := exterior_reachable_in_compl (d := 2) (by norm_num)
    (cluster 2 ω (origin 2)) R hR hr hl
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl rfl hkey







theorem icb_exitDartsSameOrbit_of_traceSurjective (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsurj : OrbitTraceSurjective (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  exitDartsSameOrbit_of_interfaceConnected (ω := ω) hfin
    ((icb_interfaceConnected_iff_traceSurjective (cluster 2 ω (origin 2))).mpr hsurj)
    (icb_exitHeads_reachable_of_far (ω := ω) hfin R hR hr hl)






theorem icb_exitFaces_reachable_of_traceSurjective (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsurj : OrbitTraceSurjective (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
      (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) :=
  exitFaces_reachable_of_sameOrbit (ω := ω) hfin
    (icb_exitDartsSameOrbit_of_traceSurjective (ω := ω) hfin hsurj R hR hr hl)







theorem icb_pc_lt_one_via_traceSurjective
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  pc_lt_one_via_dartOrbit h




































end Lattice

end StatMech
