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
import Code.Lattice.ContourAnchor
import Code.Lattice.LeftFace
import Code.Lattice.BoundaryConnected
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits

open SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}








theorem complAdj_of_unitDiff (K : Set (Site 2)) {u v : Site 2}
    (hu : u ∉ K) (hv : v ∉ K) (hd : unitWt (u - v) = 1) :
    ((hypercubicLattice 2).induce Kᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  show (hypercubicLattice 2).Adj u v
  rw [adj_iff_unitWt_sub]; exact hd


theorem complReachable_of_unitDiff (K : Set (Site 2)) {u v : Site 2}
    (hu : u ∉ K) (hv : v ∉ K) (hd : unitWt (u - v) = 1) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  (complAdj_of_unitDiff K hu hv hd).reachable



theorem complReachable_congr {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b a' b' : ↥S} (ha : (a : V) = (a' : V)) (hb : (b : V) = (b' : V))
    (h : (G.induce S).Reachable a b) : (G.induce S).Reachable a' b' := by
  rw [← Subtype.ext ha (p := fun x => x ∈ S), ← Subtype.ext hb (p := fun x => x ∈ S)]; exact h




theorem boundaryDart_head_not_mem (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    e.head ∉ K := he.2



theorem dartNext_head_not_mem (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (dartNext K e).head ∉ K := (dartNext_isBoundaryDart K e he).2
















theorem dartNext_head_sameComponent (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨e.head, he.2⟩ ⟨(dartNext K e).head, dartNext_head_not_mem K e he⟩ := by
  classical
  set t : Site 2 := -rot90Fun e.dir with ht
  have htw : unitWt t = 1 := unitWt_neg_rot90Fun_dir e
  by_cases hA : e.head + t ∈ K
  · 
    have hhead : (dartNext K e).head = e.head := (dartNext_front_head K e hA).1
    have hsub : (⟨(dartNext K e).head, dartNext_head_not_mem K e he⟩ : ↥Kᶜ)
        = ⟨e.head, he.2⟩ := Subtype.ext hhead
    rw [hsub]
  · by_cases hB : e.tail + t ∈ K
    · 
      have hhead : (dartNext K e).head = e.head + t := dartNext_straight_head K e hA hB
      have houtside : e.head + t ∉ K := hA
      have hdiff : unitWt (e.head - (e.head + t)) = 1 := by
        rw [show e.head - (e.head + t) = -t by abel, unitWt_neg]; exact htw
      have hr := complReachable_of_unitDiff K he.2 houtside hdiff
      have hsub : (⟨(dartNext K e).head, dartNext_head_not_mem K e he⟩ : ↥Kᶜ)
          = ⟨e.head + t, houtside⟩ := Subtype.ext hhead
      rw [hsub]; exact hr
    · 
      have hhead : (dartNext K e).head = e.tail + t := dartNext_left_head K e hA hB
      have hmid_out : e.head + t ∉ K := hA
      have htgt_out : e.tail + t ∉ K := hB
      have hr1 : ((hypercubicLattice 2).induce Kᶜ).Reachable
          ⟨e.head, he.2⟩ ⟨e.head + t, hmid_out⟩ := by
        apply complReachable_of_unitDiff
        rw [show e.head - (e.head + t) = -t by abel, unitWt_neg]; exact htw
      have hr2 : ((hypercubicLattice 2).induce Kᶜ).Reachable
          ⟨e.head + t, hmid_out⟩ ⟨e.tail + t, htgt_out⟩ := by
        apply complReachable_of_unitDiff
        have hsub : (e.head + t) - (e.tail + t) = e.dir := by rw [Dart.dir_def]; abel
        rw [hsub]; exact unitWt_dir e
      have hsub : (⟨(dartNext K e).head, dartNext_head_not_mem K e he⟩ : ↥Kᶜ)
          = ⟨e.tail + t, htgt_out⟩ := Subtype.ext hhead
      rw [hsub]; exact hr1.trans hr2


theorem iterate_isBoundaryDart' (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    IsBoundaryDart K ((dartNext K)^[n] e) := by
  induction n with
  | zero => simpa using he
  | succ m ih => rw [Function.iterate_succ_apply']; exact dartNext_isBoundaryDart K _ ih



theorem dartNext_iterate_head_sameComponent (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (n : ℕ) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨e.head, he.2⟩ ⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩ := by
  induction n with
  | zero => exact Reachable.refl _
  | succ m ih =>
    have hbd := iterate_isBoundaryDart' K e he m
    have hstep := dartNext_head_sameComponent K ((dartNext K)^[m] e) hbd
    have htrans := ih.trans hstep
    refine complReachable_congr (G := hypercubicLattice 2) (S := Kᶜ) rfl ?_ htrans
    show (dartNext K ((dartNext K)^[m] e)).head = ((dartNext K)^[m + 1] e).head
    rw [Function.iterate_succ_apply']



theorem dartNext_orbit_head_sameComponent (K : Set (Site 2)) (e f : Dart)
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) {n : ℕ}
    (heq : (dartNext K)^[n] e = f) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  have h := dartNext_iterate_head_sameComponent K e he n
  refine complReachable_congr (G := hypercubicLattice 2) (S := Kᶜ) rfl ?_ h
  show ((dartNext K)^[n] e).head = f.head
  rw [heq]












theorem head_compl_of_exitDartsSameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩
      ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩ := by
  obtain ⟨n, hn⟩ := h
  exact dartNext_orbit_head_sameComponent (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (leftExitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin) (leftExitDart_isBoundaryDart (ω := ω) hfin) hn















def InterfaceConnected (K : Set (Site 2)) : Prop :=
  ∀ (e f : Dart) (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f),
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ →
    ∃ n : ℕ, (dartNext K)^[n] e = f

















theorem exitDartsSameOrbit_of_interfaceConnected (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hcomp : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩
      ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩) :
    ExitDartsSameOrbit ω hfin :=
  hInt (exitDart (ω := ω) hfin) (leftExitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin) (leftExitDart_isBoundaryDart (ω := ω) hfin) hcomp


































end Lattice

end StatMech
