/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.GaussBonnet
import Code.Lattice.CrossingParity
import Code.Lattice.WindingWitness
import Code.Walls.umffullrev

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice














noncomputable def wnd_signStep (z u v : Site 2) : ℤ := by
  classical
  exact
    if (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1 then 1
    else if (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1 then -1
    else 0


theorem wnd_signStep_mem (z u v : Site 2) :
    wnd_signStep z u v = 1 ∨ wnd_signStep z u v = 0 ∨ wnd_signStep z u v = -1 := by
  classical
  unfold wnd_signStep; split_ifs <;> simp

theorem wnd_abs_signStep_le_one (z u v : Site 2) : |wnd_signStep z u v| ≤ 1 := by
  rcases wnd_signStep_mem z u v with h | h | h <;> rw [h] <;> decide



theorem wnd_signStep_ne_zero_iff (z u v : Site 2) :
    wnd_signStep z u v ≠ 0 ↔ jec_rayEdge z s(u, v) := by
  classical
  rw [jec_rayEdge_mk]
  unfold wnd_signStep
  constructor
  · intro h
    split_ifs at h with h1 h2
    · exact ⟨h1.1, Or.inl ⟨h1.2.1, h1.2.2⟩⟩
    · exact ⟨h2.1, Or.inr ⟨by omega, by omega⟩⟩
    · exact absurd rfl h
  · rintro ⟨⟨hc, hle⟩, hcase⟩
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos ⟨⟨hc, hle⟩, h1, h2⟩]; decide
    · by_cases hup : (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1
      · rw [if_pos hup]; decide
      · rw [if_neg hup, if_pos ⟨⟨hc, hle⟩, h2, h1⟩]; decide

open Classical in


theorem wnd_abs_signStep_eq_indicator (z u v : Site 2) :
    |wnd_signStep z u v| = (if jec_rayEdge z s(u, v) then 1 else 0) := by
  classical
  by_cases h : jec_rayEdge z s(u, v)
  · rw [if_pos h]
    have hne := (wnd_signStep_ne_zero_iff z u v).mpr h
    rcases wnd_signStep_mem z u v with h1 | h1 | h1
    · rw [h1]; decide
    · exact absurd h1 hne
    · rw [h1]; decide
  · rw [if_neg h]
    have : wnd_signStep z u v = 0 := by
      by_contra hc; exact h ((wnd_signStep_ne_zero_iff z u v).mp hc)
    rw [this]; decide

open Classical in



theorem wnd_signStep_parity (z u v : Site 2) :
    wnd_signStep z u v % 2 = (if jec_rayEdge z s(u, v) then (1 : ℤ) else 0) % 2 := by
  classical
  by_cases h : jec_rayEdge z s(u, v)
  · rw [if_pos h]
    have hne := (wnd_signStep_ne_zero_iff z u v).mpr h
    rcases wnd_signStep_mem z u v with h1 | h1 | h1
    · rw [h1]
    · exact absurd h1 hne
    · rw [h1]; decide
  · rw [if_neg h]
    have : wnd_signStep z u v = 0 := by
      by_contra hc; exact h ((wnd_signStep_ne_zero_iff z u v).mp hc)
    rw [this]



theorem wnd_signStep_swap (z u v : Site 2) :
    wnd_signStep z v u = - wnd_signStep z u v := by
  classical
  unfold wnd_signStep
  split_ifs <;> omega







open Classical in



noncomputable def wnd_signedCross (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℤ :=
  (w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum

@[simp] theorem wnd_signedCross_nil (z x : Site 2) :
    wnd_signedCross z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical simp [wnd_signedCross]


theorem wnd_signedCross_append (z : Site 2) {x y w' : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y w') :
    wnd_signedCross z (p.append q) = wnd_signedCross z p + wnd_signedCross z q := by
  classical
  unfold wnd_signedCross
  rw [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]




theorem wnd_signedCross_reverse (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wnd_signedCross z w.reverse = - wnd_signedCross z w := by
  classical
  unfold wnd_signedCross
  rw [SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  have hmap : (w.darts.map ((fun d => wnd_signStep z d.toProd.1 d.toProd.2) ∘ Dart.symm))
      = w.darts.map (fun d => - wnd_signStep z d.toProd.1 d.toProd.2) := by
    apply List.map_congr_left
    intro d _
    show wnd_signStep z d.symm.toProd.1 d.symm.toProd.2 = _
    rw [show d.symm.toProd.1 = d.toProd.2 from rfl, show d.symm.toProd.2 = d.toProd.1 from rfl]
    exact wnd_signStep_swap z d.toProd.1 d.toProd.2
  rw [hmap]
  rw [show (fun d : (hypercubicLattice 2).Dart => - wnd_signStep z d.toProd.1 d.toProd.2)
      = (fun x : ℤ => -x) ∘ (fun d => wnd_signStep z d.toProd.1 d.toProd.2) from rfl,
    ← List.map_map, List.sum_neg]









open Classical in


theorem wnd_rayCount_eq_darts_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (jec_rayCount z w : ℤ) =
      (w.darts.map (fun d => if jec_rayEdge z d.edge then (1 : ℤ) else 0)).sum := by
  classical
  rw [jec_rayCount, SimpleGraph.Walk.edges, List.countP_map]
  induction w.darts with
  | nil => simp
  | cons d t ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ← ih]
    by_cases h : jec_rayEdge z d.edge
    · simp only [Function.comp_apply, h, if_pos, decide_true]
      push_cast; ring
    · rw [if_neg h]
      have : ¬ (jec_rayEdge z ((Dart.edge) d)) := h
      simp only [Function.comp_apply, decide_eq_true_eq, this, if_false, Nat.add_zero,
        zero_add]




theorem wnd_signedCross_abs_le_rayCount (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    |wnd_signedCross z w| ≤ (jec_rayCount z w : ℤ) := by
  classical
  unfold wnd_signedCross
  rw [wnd_rayCount_eq_darts_sum z w]
  
  have habs : |(w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum|
      ≤ (w.darts.map (fun d => |wnd_signStep z d.toProd.1 d.toProd.2|)).sum := by
    induction w.darts with
    | nil => simp
    | cons d t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      calc |wnd_signStep z d.toProd.1 d.toProd.2
              + (t.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum|
          ≤ |wnd_signStep z d.toProd.1 d.toProd.2|
              + |(t.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum| :=
            abs_add_le _ _
        _ ≤ |wnd_signStep z d.toProd.1 d.toProd.2|
              + (t.map (fun d => |wnd_signStep z d.toProd.1 d.toProd.2|)).sum := by linarith
  refine le_trans habs (le_of_eq ?_)
  congr 1
  apply List.map_congr_left
  intro d _
  rw [wnd_abs_signStep_eq_indicator z d.toProd.1 d.toProd.2]
  rw [show d.edge = s(d.toProd.1, d.toProd.2) from rfl]





theorem wnd_signedCross_parity (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wnd_signedCross z w % 2 = (jec_rayCount z w : ℤ) % 2 := by
  classical
  unfold wnd_signedCross
  rw [wnd_rayCount_eq_darts_sum z w]
  
  induction w.darts with
  | nil => simp
  | cons d t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      Int.add_emod, Int.add_emod (if jec_rayEdge z d.edge then (1 : ℤ) else 0), ih]
    have hstep : wnd_signStep z d.toProd.1 d.toProd.2 % 2
        = (if jec_rayEdge z d.edge then (1 : ℤ) else 0) % 2 := by
      rw [wnd_signStep_parity z d.toProd.1 d.toProd.2,
        show d.edge = s(d.toProd.1, d.toProd.2) from rfl]
    rw [hstep]














theorem wnd_signedCross_ne_zero_of_rayCount_odd (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w ≠ 0 := by
  classical
  have hpar := wnd_signedCross_parity z w
  rw [Nat.not_even_iff] at hodd
  have hrayodd : (jec_rayCount z w : ℤ) % 2 = 1 := by
    have hc : ((jec_rayCount z w : ℤ) % 2) = ((jec_rayCount z w % 2 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hc, hodd]; rfl
  intro hz
  rw [hz] at hpar
  simp only [Int.zero_emod] at hpar
  rw [hrayodd] at hpar
  exact absurd hpar.symm (by decide)





















def wnd_SignedCrossEqRevCount (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) : Prop :=
  wnd_signedCross z (olb_orbitLoop K hK a.1 a.2) = revCount K a




def wnd_SignedCrossPMone (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) : Prop :=
  wnd_signedCross z (olb_orbitLoop K hK a.1 a.2) = 1 ∨
    wnd_signedCross z (olb_orbitLoop K hK a.1 a.2) = -1





theorem wnd_orbitLoop_signedCross_ne_zero (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_signedCross z (olb_orbitLoop K hK a.1 a.2) ≠ 0 :=
  wnd_signedCross_ne_zero_of_rayCount_odd z (olb_orbitLoop K hK a.1 a.2) hodd





theorem wnd_revCount_ne_zero_of_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hbridge : wnd_SignedCrossEqRevCount K hK a z)
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    revCount K a ≠ 0 := by
  unfold wnd_SignedCrossEqRevCount at hbridge
  rw [← hbridge]
  exact wnd_orbitLoop_signedCross_ne_zero K hK a z hodd





theorem wnd_revCount_pm_one_of_residues (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hbridge : wnd_SignedCrossEqRevCount K hK a z)
    (hpm : wnd_SignedCrossPMone K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 := by
  unfold wnd_SignedCrossEqRevCount at hbridge
  unfold wnd_SignedCrossPMone at hpm
  rw [← hbridge]
  exact hpm






theorem wnd_eulerCharOne_of_residues (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hbridge : wnd_SignedCrossEqRevCount K hK a z)
    (hpm : wnd_SignedCrossPMone K hK a z) :
    EulerCharOne K a :=
  umf_eulerCharOne_of_revCount_pm_one K a hp
    (wnd_revCount_pm_one_of_residues K hK a z hbridge hpm)













theorem wnd_unitSquareLoop_signedCross :
    wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
  unfold wwit_unitSquareLoop wnd_signedCross
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map,
    List.sum_append, List.sum_reverse]
  decide




theorem wnd_unitSquareLoop_signedCross_ne_zero :
    wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop ≠ 0 :=
  wnd_signedCross_ne_zero_of_rayCount_odd (![1, 1] : Site 2) wwit_unitSquareLoop
    wwit_unitSquareLoop_inside_odd

































end Lattice

end StatMech
