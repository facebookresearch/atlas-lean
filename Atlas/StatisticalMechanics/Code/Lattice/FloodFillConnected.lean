/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.EulerGeometricFaces

open Set SimpleGraph Function

namespace StatMech

namespace Lattice







def ffc_offSupportLattice (B : Set (Site 2)) : SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ x ∉ B ∧ y ∉ B
  symm := by
    rintro x y ⟨hadj, hx, hy⟩
    exact ⟨hadj.symm, hy, hx⟩
  loopless := ⟨fun x h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem ffc_offSupportLattice_adj (B : Set (Site 2)) (x y : Site 2) :
    (ffc_offSupportLattice B).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ x ∉ B ∧ y ∉ B := Iff.rfl


theorem ffc_offSupportLattice_le (B : Set (Site 2)) :
    ffc_offSupportLattice B ≤ hypercubicLattice 2 := fun _ _ h => h.1




theorem ffc_offSupportWalk_support {B : Set (Site 2)} {x y : Site 2}
    (w : (ffc_offSupportLattice B).Walk x y) (hx : x ∉ B) :
    ∀ z ∈ w.support, z ∉ B := by
  induction w with
  | nil => intro z hz; rw [SimpleGraph.Walk.support_nil] at hz; rw [List.mem_singleton] at hz;
           exact hz ▸ hx
  | @cons a b c hab p ih =>
    intro z hz
    have hb : b ∉ B := hab.2.2
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact ih hb z h




theorem ffc_project_walk {B : Set (Site 2)} {x y : Site 2}
    (w : (ffc_offSupportLattice B).Walk x y) (hx : x ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk x y, (∀ z ∈ p.support, z ∉ B) ∧ p.support = w.support := by
  classical
  refine ⟨w.mapLe (ffc_offSupportLattice_le B), ?_, ?_⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
    exact ffc_offSupportWalk_support w hx z hz
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]





def ffc_lift_walk {B : Set (Site 2)} :
    ∀ {x y : Site 2} (p : (hypercubicLattice 2).Walk x y),
      (∀ z ∈ p.support, z ∉ B) → (ffc_offSupportLattice B).Walk x y
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons hab p, hp =>
      SimpleGraph.Walk.cons
        ⟨hab, hp _ (by simp), hp _ (by
          rw [SimpleGraph.Walk.support_cons]; right; exact p.start_mem_support)⟩
        (ffc_lift_walk p (fun z hz => hp z (by
          rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)))







theorem ffc_reachable_iff_offSupportWalk {B : Set (Site 2)} {x y : Site 2} (hx : x ∉ B) :
    (ffc_offSupportLattice B).Reachable x y ↔
      ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
  constructor
  · rintro ⟨w⟩
    obtain ⟨p, hp, _⟩ := ffc_project_walk w hx
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨ffc_lift_walk p hp⟩













def ffc_floodFill (B : Set (Site 2)) (seed : Site 2) : Set (Site 2) :=
  {z | (ffc_offSupportLattice B).Reachable seed z}

@[simp] theorem ffc_mem_floodFill {B : Set (Site 2)} {seed z : Site 2} :
    z ∈ ffc_floodFill B seed ↔ (ffc_offSupportLattice B).Reachable seed z := Iff.rfl



theorem ffc_seed_mem_floodFill (B : Set (Site 2)) (seed : Site 2) :
    seed ∈ ffc_floodFill B seed :=
  SimpleGraph.Reachable.refl _




theorem ffc_floodFill_offSupport {B : Set (Site 2)} {seed : Site 2} (hseed : seed ∉ B)
    {z : Site 2} (hz : z ∈ ffc_floodFill B seed) : z ∉ B := by
  rw [ffc_mem_floodFill] at hz
  obtain ⟨w⟩ := hz
  exact ffc_offSupportWalk_support w hseed z w.end_mem_support




theorem ffc_floodFill_reachable_offSupportLattice {B : Set (Site 2)} {seed : Site 2}
    {x y : Site 2} (hx : x ∈ ffc_floodFill B seed) (hy : y ∈ ffc_floodFill B seed) :
    (ffc_offSupportLattice B).Reachable x y := by
  rw [ffc_mem_floodFill] at hx hy
  exact hx.symm.trans hy








theorem ffc_floodFill_path_connected_offSupport {B : Set (Site 2)} {seed : Site 2}
    (hseed : seed ∉ B) {x y : Site 2}
    (hx : x ∈ ffc_floodFill B seed) (hy : y ∈ ffc_floodFill B seed) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
  have hxB : x ∉ B := ffc_floodFill_offSupport hseed hx
  exact (ffc_reachable_iff_offSupportWalk hxB).mp
    (ffc_floodFill_reachable_offSupportLattice hx hy)




theorem ffc_floodFill_self_offSupport_walk {B : Set (Site 2)} {seed : Site 2} (hseed : seed ∉ B)
    {z : Site 2} (hz : z ∈ ffc_floodFill B seed) :
    ∃ p : (hypercubicLattice 2).Walk seed z, ∀ w ∈ p.support, w ∉ B :=
  ffc_floodFill_path_connected_offSupport hseed (ffc_seed_mem_floodFill B seed) hz







theorem ffc_floodFill_step {B : Set (Site 2)} {seed z w : Site 2}
    (hz : z ∈ ffc_floodFill B seed) (hadj : (hypercubicLattice 2).Adj z w)
    (hzB : z ∉ B) (hwB : w ∉ B) :
    w ∈ ffc_floodFill B seed := by
  rw [ffc_mem_floodFill] at hz ⊢
  exact hz.trans ((ffc_offSupportLattice_adj B z w).mpr ⟨hadj, hzB, hwB⟩).reachable







theorem ffc_engine_nonvacuous :
    ∃ p : (hypercubicLattice 2).Walk (![0, 0] : Site 2) ![1, 0],
      ∀ z ∈ p.support, z ∉ ({z | z = (![5, 5] : Site 2)} : Set (Site 2)) := by
  set B : Set (Site 2) := {z | z = (![5, 5] : Site 2)} with hB
  have hseed : (![0, 0] : Site 2) ∉ B := by
    simp only [hB, Set.mem_setOf_eq]; intro h; have := congrFun h 0; simp at this
  have hadj : (hypercubicLattice 2).Adj (![0, 0] : Site 2) ![1, 0] := by
    rw [hypercubicLattice_adj]; decide
  have htgt : (![1, 0] : Site 2) ∉ B := by
    simp only [hB, Set.mem_setOf_eq]; intro h; have := congrFun h 0; simp at this
  have hmem : (![1, 0] : Site 2) ∈ ffc_floodFill B (![0, 0] : Site 2) :=
    ffc_floodFill_step (ffc_seed_mem_floodFill B _) hadj hseed htgt
  exact ffc_floodFill_path_connected_offSupport hseed (ffc_seed_mem_floodFill B _) hmem














theorem ffc_floodFill_reachable_in_barrier {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) {x y : Site 2}
    (hx : x ∈ ffc_floodFill {z | z ∈ Vc.support} seed)
    (hy : y ∈ ffc_floodFill {z | z ∈ Vc.support} seed) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
  obtain ⟨p, hp⟩ := ffc_floodFill_path_connected_offSupport hseed hx hy
  exact jlri_offSupport_walk_in_barrier Vc p hp








theorem ffc_side_reachable_of_eq_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) {T : Set (Site 2)}
    (hT : T = ffc_floodFill {z | z ∈ Vc.support} seed) {x y : Site 2} (hx : x ∈ T) (hy : y ∈ T) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  ffc_floodFill_reachable_in_barrier Vc hseed (hT ▸ hx) (hT ▸ hy)





theorem ffc_floodFill_inside_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support)
    (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} seed)
    {x y : Site 2} (hx : x ∈ jec_leftRegion Vc) (hy : y ∈ jec_leftRegion Vc) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  ffc_side_reachable_of_eq_floodFill Vc hseed hInside hx hy




theorem ffc_floodFill_outside_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support)
    (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} seed)
    {x y : Site 2} (hx : x ∉ jec_leftRegion Vc) (hy : y ∉ jec_leftRegion Vc) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  ffc_side_reachable_of_eq_floodFill Vc hseed hOutside hx hy












theorem ffc_hInOff_of_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support)
    (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
  intro s t hs ht
  exact ffc_floodFill_path_connected_offSupport hseed (hInside ▸ hs) (hInside ▸ ht)





theorem ffc_hOutOff_of_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support)
    (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} seed) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
  intro s t hs ht
  have hs' : s ∈ (jec_leftRegion Vc)ᶜ := hs
  have ht' : t ∈ (jec_leftRegion Vc)ᶜ := ht
  exact ffc_floodFill_path_connected_offSupport hseed (hOutside ▸ hs') (hOutside ▸ ht')












theorem ffc_two_components_of_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    {sIn sOut : Site 2} (hsIn : sIn ∉ Vc.support) (hsOut : sOut ∉ Vc.support)
    (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} sIn)
    (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} sOut) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  jlri_two_components_of_offSupport_connected Vc hp hq
    (ffc_hInOff_of_floodFill Vc hsIn hInside)
    (ffc_hOutOff_of_floodFill Vc hsOut hOutside)















theorem ffc_egf_LoopFloodFill_of_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {xIn yOut : Site 2} (hxIn : xIn ∈ jec_leftRegion Vc) (hyOut : yOut ∉ jec_leftRegion Vc)
    {sIn sOut : Site 2} (hsIn : sIn ∉ Vc.support) (hsOut : sOut ∉ Vc.support)
    (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} sIn)
    (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} sOut) :
    egf_LoopFloodFill Vc := by
  refine ⟨⟨xIn, hxIn⟩, ⟨yOut, hyOut⟩, ?_, ?_⟩
  · intro p q hp hq
    exact ffc_floodFill_inside_connected Vc hsIn hInside hp hq
  · intro p q hp hq
    exact ffc_floodFill_outside_connected Vc hsOut hOutside hp hq






theorem ffc_egf_loop_two_components_of_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {xIn yOut : Site 2} (hxIn : xIn ∈ jec_leftRegion Vc) (hyOut : yOut ∉ jec_leftRegion Vc)
    {sIn sOut : Site 2} (hsIn : sIn ∉ Vc.support) (hsOut : sOut ∉ Vc.support)
    (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} sIn)
    (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} sOut) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  egf_loop_two_components Vc
    (ffc_egf_LoopFloodFill_of_floodFill Vc hxIn hyOut hsIn hsOut hInside hOutside)

end Lattice

end StatMech
