/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib
import Code.Percolation.DctItem2
import Code.Sharpness.PivotalFactorFull

open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech

namespace StatMech
namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem internal_edge_ne_boundary {S : Finset (Site d)} {x y : Site d}
    (hx : x ∈ S) (hy : y ∉ S) {e : Sym2 (Site d)}
    (he : e ∈ Sharpness.internalEdges (S : Set (Site d))) : e ≠ s(x, y) := by
  rintro rfl
  obtain ⟨a, ha, b, hb, hab⟩ := he
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hy hb
  · exact hy ha









theorem pivotal_of_surface_imp_withinConn {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S) (h0S : origin d ∈ S)
    {x y : Site d} (hadj : (hypercubicLattice d).Adj x y)
    (hxS : x ∈ S) (hybox : y ∈ box d n) (hyS : y ∉ S)
    (hpiv : IsPivotal (s(x, y) : Sym2 (Site d)) (boxCrossingEvent d n) ω) :
    ω ∈ withinConnEvent d (S : Set (Site d)) (origin d) x := by
  classical
  let e : Sym2 (Site d) := s(x, y)
  have hxy : x ≠ y := hadj.ne
  have hopenEvent : setOpen e ω ∈ boxCrossingEvent d n := by
    exact ((isPivotal_iff_of_isIncreasing (boxCrossingEvent_isIncreasing n) ω).mp hpiv).2
  obtain ⟨z, hzbox, hzbdry, h0box, hreach⟩ := hopenEvent
  have hzS : z ∉ (S : Set (Site d)) := by
    intro hz
    have hzsurf : z ∈ surfaceSet d n ω := hS ▸ (by exact_mod_cast hz)
    have hncb := (mem_surfaceSet.mp hzsurf).2
    exact hncb ⟨hzbox, z, hzbox, hzbdry, SimpleGraph.Reachable.refl _⟩
  obtain ⟨w⟩ := hreach
  let T : Set ↥(box d n) := {v | (v : Site d) ∈ (S : Set (Site d))}
  have h0T : (⟨origin d, h0box⟩ : ↥(box d n)) ∈ T := by
    exact_mod_cast h0S
  have hzT : (⟨z, hzbox⟩ : ↥(box d n)) ∉ T := by
    exact hzS
  obtain ⟨a, b, haS, hbS, hab, ⟨pref⟩⟩ :=
    firstExit w T h0T hzT
  have habOpen : IsOpenEdge d (setOpen e ω) (a : Site d) (b : Site d) := by
    simpa only [openSubgraphInduce_adj, openSubgraph_adj] using hab
  have hbbox : (b : Site d) ∈ box d n := b.2
  have habClosed : ω s((a : Site d), (b : Site d)) = false :=
    surface_boundary_edge_closed hS habOpen.1 (by exact_mod_cast haS) hbbox
      (by exact hbS)
  have hedge : s((a : Site d), (b : Site d)) = e := by
    by_contra hne
    have hopenEq : (setOpen e ω) s((a : Site d), (b : Site d)) =
        ω s((a : Site d), (b : Site d)) := StatMech.setOpen_of_ne hne ω
    have ht : (setOpen e ω) s((a : Site d), (b : Site d)) = true := habOpen.2
    rw [hopenEq, habClosed] at ht
    exact Bool.false_ne_true ht
  have ha : (a : Site d) = x := by
    rw [show e = s(x, y) from rfl, Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · exact h.1
    · exfalso
      exact hyS (h.1 ▸ (show (a : Site d) ∈ S from haS))
  have hagree : ∀ j ∈ Sharpness.internalEdges (S : Set (Site d)),
      (setOpen e ω) j = ω j := by
    intro j hj
    apply StatMech.setOpen_of_ne
    simpa only [e] using internal_edge_ne_boundary hxS hyS hj
  let mapToS : T → ↥(S : Set (Site d)) := fun v => ⟨(v.1 : Site d), v.2⟩
  let homToS :
      (openSubgraphInduce d (setOpen e ω) (box d n)).induce T →g
        openSubgraphInduce d (setOpen e ω) (S : Set (Site d)) := ⟨mapToS, by
      intro u v huv
      exact huv⟩
  have hconnOpen : ConnectedWithin d (setOpen e ω) (S : Set (Site d))
      ⟨origin d, by exact_mod_cast h0S⟩ ⟨(a : Site d), haS⟩ := by
    refine ⟨?w⟩
    exact (pref.map homToS).copy rfl rfl
  have hconn := Sharpness.shp_connWithin_transfer hagree hconnOpen
  refine ⟨by exact_mod_cast h0S, by exact_mod_cast hxS, ?_⟩
  simpa only [ha] using hconn



theorem pivotal_surface_event_eq_withinConn {n : ℕ} {S : Finset (Site d)}
    (h0S : origin d ∈ S) (hSinner : (S : Set (Site d)) ⊆ box d (n - 1))
    (hn : 1 ≤ n) {e : Site d × Site d} (he : e ∈ boundaryEdges d S) :
    pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S =
      withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ surfaceEvent d n S := by
  ext ω
  constructor
  · rintro ⟨hpiv, hsurf⟩
    obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer he
    have hadj := boundaryEdges_adj he
    have h2box := boundaryEdges_snd_mem_box hn hSinner he
    exact ⟨pivotal_of_surface_imp_withinConn hsurf h0S hadj h1S h2box h2S hpiv, hsurf⟩
  · intro h
    have hs := withinConn_surf_subset_pivotalClosed h0S hSinner hn he h
    exact ⟨hs.1.1, hs.2⟩





theorem pivotal_surface_factor (p : ℝ≥0) (hp : p ≤ 1)
    {n : ℕ} {S : Finset (Site d)} (h0S : origin d ∈ S)
    (hSinner : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n)
    {e : Site d × Site d} (he : e ∈ boundaryEdges d S) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S) =
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) e.1) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (surfaceEvent d n S) := by
  rw [pivotal_surface_event_eq_withinConn h0S hSinner hn he]
  exact surface_withinConn_indep p hp n S (origin d) e.1

end Percolation
end StatMech
