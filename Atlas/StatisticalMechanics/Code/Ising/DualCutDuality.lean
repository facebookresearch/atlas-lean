/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.Ising.KWClosedWalkParity
import Code.Ising.DualWalkBoundsClose
import Code.Lattice.CrossingParity
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.JordanCycleSpace

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising





section ReachRegion

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}




def primalMinus (Gp : SimpleGraph V) (δ : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := Gp.Adj x y ∧ s(x, y) ∉ δ
  symm := by
    intro x y ⟨hadj, hbd⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => Gp.irrefl h.1⟩

omit [DecidableEq V] in
@[simp] theorem primalMinus_adj (δ : Finset (Sym2 V)) (x y : V) :
    (primalMinus Gp δ).Adj x y ↔ Gp.Adj x y ∧ s(x, y) ∉ δ := Iff.rfl

omit [DecidableEq V] in
theorem primalMinus_le (δ : Finset (Sym2 V)) : primalMinus Gp δ ≤ Gp := fun _ _ h => h.1




theorem walkParity_mapLe_primalMinus {δ : Finset (Sym2 V)} {x y : V}
    (p : (primalMinus Gp δ).Walk x y) :
    walkParity Gp δ (p.mapLe (primalMinus_le δ)) = false := by
  induction p with
  | nil => simp
  | @cons u v w hadj q ih =>
    have hmem : s(u, v) ∉ δ := hadj.2
    rw [show (SimpleGraph.Walk.cons hadj q).mapLe (primalMinus_le δ)
          = SimpleGraph.Walk.cons (G := Gp) hadj.1 (q.mapLe (primalMinus_le δ)) from rfl,
      walkParity_cons, decide_eq_false hmem, Bool.false_xor, ih]











theorem primalMinus_sameSide_of_reachable {δ : Finset (Sym2 V)} (hev : EvenOnCycles Gp δ)
    (hG : Gp.Preconnected) (v₀ : V) {x y : V} (hr : (primalMinus Gp δ).Reachable x y) :
    parityConfig Gp δ hG v₀ x = parityConfig Gp δ hG v₀ y := by
  obtain ⟨p⟩ := hr
  have hpx : parityConfig Gp δ hG v₀ x
      = walkParity Gp δ (hG v₀ x).some := rfl
  set px : Gp.Walk v₀ x := (hG v₀ x).some with hpxdef
  set pxy : Gp.Walk x y := p.mapLe (primalMinus_le δ) with hpxydef
  have hpy : parityConfig Gp δ hG v₀ y
      = walkParity Gp δ (px.append pxy) :=
    walkParity_eq_of_evenOnCycles hev (hG v₀ y).some (px.append pxy)
  rw [hpy, walkParity_append, walkParity_mapLe_primalMinus, Bool.xor_false]
  rfl




















theorem primalMinus_separates_of_mem {δ : Finset (Sym2 V)} (hev : EvenOnCycles Gp δ)
    {u v : V} (hadj : Gp.Adj u v) (hmem : s(u, v) ∈ δ) :
    ¬ (primalMinus Gp δ).Reachable u v := by
  rintro ⟨puv⟩
  have hpar0 : walkParity Gp δ (puv.mapLe (primalMinus_le δ)) = false :=
    walkParity_mapLe_primalMinus puv
  let closing : Gp.Walk v u := SimpleGraph.Walk.cons hadj.symm (.nil : Gp.Walk u u)
  let loop : Gp.Walk u u := (puv.mapLe (primalMinus_le δ)).append closing
  have hloop : walkParity Gp δ loop = false := hev u loop
  rw [walkParity_append, hpar0, Bool.false_xor] at hloop
  have hclose : walkParity Gp δ closing = true := by
    show walkParity Gp δ (SimpleGraph.Walk.cons hadj.symm (.nil : Gp.Walk u u)) = true
    rw [walkParity_cons, walkParity_nil, Bool.xor_false, Sym2.eq_swap]
    exact decide_eq_true hmem
  rw [hclose] at hloop
  exact Bool.noConfusion hloop
















theorem parityConfig_isRegion {δ : Finset (Sym2 V)} (hev : EvenOnCycles Gp δ)
    (hG : Gp.Preconnected) (v₀ : V) {u v : V} (hadj : Gp.Adj u v) :
    s(u, v) ∈ δ ↔ parityConfig Gp δ hG v₀ u ≠ parityConfig Gp δ hG v₀ v := by
  have hx := parityConfig_adj_xor hev hG v₀ hadj
  constructor
  · intro hmem
    rw [decide_eq_true hmem] at hx
    revert hx
    cases parityConfig Gp δ hG v₀ u <;> cases parityConfig Gp δ hG v₀ v <;> simp
  · intro hne
    by_contra hnm
    rw [decide_eq_false hnm] at hx
    revert hx hne
    cases parityConfig Gp δ hG v₀ u <;> cases parityConfig Gp δ hG v₀ v <;> simp

end ReachRegion









section LatticeWindingRegion

open StatMech.Lattice






theorem dcd_latticeMinusBarrier_sameSide (S : Set (Site 2)) {x y : Site 2}
    (w : (latticeMinusBarrier S).Walk x y) : (x ∈ S ↔ y ∈ S) :=
  latticeMinusBarrier_sameSide S w





theorem dcd_not_reachable_latticeMinusBarrier (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (latticeMinusBarrier S).Reachable x y :=
  not_reachable_latticeMinusBarrier S hx hy







theorem dcd_windingRegion_separates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∈ jec_leftRegion Vc) (hy : y ∉ jec_leftRegion Vc) :
    ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  not_reachable_latticeMinusBarrier (jec_leftRegion Vc) hx hy






theorem dcd_windingRegion_bdEdge_on_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd





theorem dcd_windingRegion_no_bdEdge_off_support {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    ¬ bdEdge (jec_leftRegion Vc) s(u, v) :=
  jlri_no_bdEdge_off_support Vc hadj hu hv

















theorem dcd_boundsRegion_at_walk_of_bdEdge
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (S : Set (Site 2)) {w : Site 2}
    (W : Gd.Walk w w)
    (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))) :
    ∃ S' : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ S' u ≠ S' v) :=
  latticeSide_boundsRegion_of_pullback_eq_bdEdge S W (fun h => hpull h)












theorem dcd_boundsRegion_of_leftRegionMatch {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hmatch : ∀ {w : Site 2} (W : Gd.Walk w w), DualWalkLeftRegionMatch W) :
    DualWalkBoundsRegion (hypercubicLattice 2) Gd crossEdge :=
  dualWalkBoundsRegion_lattice_of_bdEdgeMatch
    (latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch hmatch)













theorem dcd_two_components_of_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  jlri_two_components_of_offSupport_connected Vc hp hq hInOff hOutOff













theorem dcd_leftRegionMatch_of_edgeless {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hGd : Gd.edgeSet = ∅) {w : Site 2} (W : Gd.Walk w w) :
    DualWalkLeftRegionMatch W := by
  refine ⟨w, SimpleGraph.Walk.nil, ?_⟩
  intro u v _
  
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image crossEdge.symm = (∅ : Finset (Sym2 (Site 2))) := by
    rw [hnil]; simp
  
  have hleft : ∀ z : Site 2,
      z ∉ jec_leftRegion (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk w w) := by
    intro z
    rw [jec_mem_leftRegion]
    simp [jec_rayCount_nil]
  rw [hempty]
  constructor
  · intro hmem; exact absurd hmem (Finset.notMem_empty _)
  · intro hbd
    rw [bdEdge_mk] at hbd
    exact absurd hbd (by simp [hleft u, hleft v])

end LatticeWindingRegion




























end Ising

end StatMech
