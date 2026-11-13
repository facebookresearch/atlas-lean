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

open Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice



















theorem kc_offsupport_rayParity_const {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
  induction p with
  | nil => exact Iff.rfl
  | @cons b c d hbc q ih =>
    
    have hboff : b ∉ Vc.support := hp b (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self ..)
    have hcoff : c ∉ Vc.support := hp c (by
      rw [SimpleGraph.Walk.support_cons]; right; exact q.start_mem_support)
    have hq : ∀ w ∈ q.support, w ∉ Vc.support := fun w hw =>
      hp w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    
    exact (jec_localConstancy Vc hbc hboff hcoff).trans (ih hq)










theorem kc_offsupport_leftRegion_const {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
  simp only [jec_mem_leftRegion]
  exact not_congr (kc_offsupport_rayParity_const Vc p hp)




theorem kc_offsupport_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support) (hx : x ∈ jec_leftRegion Vc) :
    y ∈ jec_leftRegion Vc :=
  (kc_offsupport_leftRegion_const Vc p hp).mp hx




theorem kc_offsupport_notMem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support) (hx : x ∉ jec_leftRegion Vc) :
    y ∉ jec_leftRegion Vc :=
  fun hy => hx ((kc_offsupport_leftRegion_const Vc p hp).mpr hy)














theorem kc_offsupport_rayParity_const_all {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    ∀ w ∈ p.support, (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount w Vc)) := by
  induction p with
  | nil =>
    intro w hw
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    subst hw; exact Iff.rfl
  | @cons b c d hbc q ih =>
    have hboff : b ∉ Vc.support := hp b (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self ..)
    have hcoff : c ∉ Vc.support := hp c (by
      rw [SimpleGraph.Walk.support_cons]; right; exact q.start_mem_support)
    have hq : ∀ w ∈ q.support, w ∉ Vc.support := fun w hw =>
      hp w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    have hstep := jec_localConstancy Vc hbc hboff hcoff
    have ihq := ih hq
    intro w hw
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with h | h
    · subst h; exact Iff.rfl
    · exact hstep.trans (ihq w h)




theorem kc_offsupport_leftRegion_const_all {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    ∀ w ∈ p.support, (x ∈ jec_leftRegion Vc ↔ w ∈ jec_leftRegion Vc) := by
  intro w hw
  simp only [jec_mem_leftRegion]
  exact not_congr (kc_offsupport_rayParity_const_all Vc p hp w hw)

end Walls

end StatMech
